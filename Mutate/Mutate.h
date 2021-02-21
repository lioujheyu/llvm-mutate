#include <stdio.h>
#include <cstdlib>
#include <ctime>
#include <random>
#include <fstream>
#include <algorithm>
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

using namespace llvm;

std::random_device rd;
std::mt19937 gen(rd());
const std::string ldgPre = "llvm.nvvm.ldg.global";

StringRef getUID(const Instruction *I) {
    if (!I)
        assert(0);

    if (I->hasMetadata("uniqueID")) {
        MDNode* N = I->getMetadata("uniqueID");
        StringRef UID = cast<MDString>(N->getOperand(0))->getString();
        return UID;
    }
    else
        return StringRef();
}

StringRef getUID(const Instruction &I) { return getUID(&I); }

void setUID(Instruction *I, std::string UID) {
    if (!I)
        assert(0);

    LLVMContext& C = I->getContext();
    MDNode* N = MDNode::get(C, MDString::get(C, UID));
    I->setMetadata("uniqueID", N);
}

void setUID(Instruction *I, StringRef UID) { setUID(I, UID.str()); }

Value* getConstantValue(Type* T)
{
    switch(T->getTypeID()) {
    case Type::IntegerTyID: case Type::FixedVectorTyID:
        return Constant::getIntegerValue(T, APInt(T->getScalarType()->getIntegerBitWidth(), 1));
    case Type::HalfTyID:    case Type::FloatTyID:
    case Type::DoubleTyID:
        return ConstantFP::get(T, StringRef("1"));
    case Type::X86_FP80TyID:  case Type::FP128TyID:
    case Type::PPC_FP128TyID: case Type::PointerTyID:
    case Type::StructTyID:    case Type::ArrayTyID:
        return Constant::getNullValue(T);
    default:
        assert(0);
    }
}

void CollectValueBeforeI(Function *F, Instruction* boundary, Value* refOP,
                           std::vector<std::pair<Value*, StringRef>> &resultVec)
{
    Type *T = (refOP != NULL)? refOP->getType() : NULL;
    for (Argument &A : F->args()) {
        if (T != NULL) {
            if (A.getType() != T)
                continue;
        }
        resultVec.push_back(std::make_pair(&A, A.getName()));
    }

    DominatorTree DT = DominatorTree(*F);
    for (Instruction &I : instructions(F)) {
        if (boundary != NULL) {
            if (&I == boundary)
                break;
            if (DT.dominates(&I, boundary) == false)
                continue;
        }
        if (&I == refOP)
            continue;
        if (I.getType()->isVoidTy())
            continue;
        if (I.getName().find("nop") != StringRef::npos)
            continue;
        if (T != NULL) {
            if (I.getType() != T)
                continue;
            if (T->isPointerTy()) {
                if (I.getType()->getPointerElementType() !=
                    T->getPointerElementType())
                    continue;
            }
        }
        resultVec.push_back(std::make_pair(&I, I.getName()));
    }
}

std::pair<Value*, StringRef> randValue(Module &M)
{
    std::vector<std::pair<Value*, StringRef>> resultVec;
    for (Function &F : M) {
        if (F.empty())
            continue;
        CollectValueBeforeI(&F, NULL, NULL, resultVec);
    }

    std::uniform_int_distribution<> randIdx(0, resultVec.size()-1);
    return resultVec[randIdx(gen)];
}

std::pair<Value*, StringRef> randValueBeforeI(Function *F, Instruction* boundary, Value* refOP)
{
    std::vector<std::pair<Value*, StringRef>> resultVec;
    CollectValueBeforeI(F, boundary, refOP, resultVec);
    // has constant to participate in drawing
    resultVec.push_back(std::make_pair(getConstantValue(refOP->getType()), StringRef("C1")));

    std::uniform_int_distribution<> randIdx(0, resultVec.size()-1);
    return resultVec[randIdx(gen)];
}

void CollectOperandAfterI(Function &F, Instruction* boundary, Type* T,
                          std::vector<std::pair<Instruction*, unsigned>> &OPvec) {

    DominatorTree DT = DominatorTree(F);

    if (boundary == NULL) { // Get the all from the function
        for (Instruction &I : instructions(F)) {
            if (I.getName().find("nop"))
                continue;
            for (unsigned i=0; i<I.getNumOperands(); i++) {
                Value *op = I.getOperand(i);
                if (T == NULL)
                    OPvec.push_back(std::make_pair(&I, i));
                else if (op->getType() == T)
                    OPvec.push_back(std::make_pair(&I, i));
            }
        }
    }
    else{ // has a boundary.
        bool reached = false;
        for (Instruction &I : instructions(F)) {
            if (I.getName().find("nop") != StringRef::npos)
                continue;
            if (DT.dominates(boundary, &I) == false)
                continue;

            for (unsigned i=0; i<I.getNumOperands(); i++) {
                Value *op = I.getOperand(i);
                if (op == boundary)
                    continue;
                // TODO: generate constant value for this GEP corner case
                if(isa<GetElementPtrInst>(I)) {
                    GetElementPtrInst *GEP = cast<GetElementPtrInst>(&I);
                    if (GEP->getSourceElementType()->isStructTy())
                        break;
                }

                if (T == NULL)
                    OPvec.push_back(std::make_pair(&I, i));
                else if (op->getType() == T)
                    OPvec.push_back(std::make_pair(&I, i));
            }
        }
    }
}

std::pair<Instruction*, unsigned> randOperandAfterI(Function &F, Instruction* boundary, Type* T) 
{
    std::vector<std::pair<Instruction*, unsigned>> OPvec;
    CollectOperandAfterI(F, boundary, T, OPvec);

    Instruction* dummy = NULL;
    if (OPvec.empty())
        return std::make_pair(dummy, 0);

    std::uniform_int_distribution<> randIdx(0, OPvec.size()-1);
    return OPvec[randIdx(gen)];
}

std::pair<Instruction*, StringRef> randTexCachableI(Module &M)
{
    std::vector<std::pair<Instruction*, StringRef>> resultVec;
    for (Function &F : M)
    for (BasicBlock &BB : F)
    for (Instruction &I : BB) {
        if (isa<LoadInst>(I)) {
            // induce the source address space and only allow global space
            // LLVM seems to have addrspacecast for shared before using it
            // Need to monitor if there is any false assumption with this method
            Instruction *srcI = dyn_cast_or_null<Instruction>(I.getOperand(0));
            if (srcI == NULL)
                continue;
            if (isa<AddrSpaceCastInst>(srcI)) {
                if (srcI->getOperand(0)->getType()->getPointerAddressSpace() == 3)
                    continue;
            }
            // if (isa<GetElementPtrInst>(srcI)) {
            //     if (srcI->getOperand(0)->getType()->getPointerAddressSpace() != 1)
            //         continue;
            // }

            resultVec.push_back(std::make_pair(&I, I.getName()));
        }
        else if (isa<CallInst>(I)) {
            CallInst* calI = cast<CallInst>(&I);
            if (calI->isIndirectCall())
                continue;
            if (isa<InlineAsm>(calI->getCalledOperand())) {
                InlineAsm *inlineasm = cast<InlineAsm>(calI->getCalledOperand());
                if (inlineasm->getAsmString().find("ld.global.cg") != std::string::npos)
                    resultVec.push_back(std::make_pair(&I, I.getName()));
            }
            else if (calI->getCalledFunction()->getName().contains(ldgPre))
                resultVec.push_back(std::make_pair(&I, I.getName()));
        }
    }

    std::uniform_int_distribution<> randIdx(0, resultVec.size()-1);
    return resultVec[randIdx(gen)];
}

// Force to use the result of instruction tI somewhere later.
void useResult(Instruction *tI){
    std::pair<Instruction*, unsigned> result;
    result = randOperandAfterI(*(tI->getFunction()), tI, tI->getType());

    if (result.first == NULL) {
        errs()<<"could find no use for result\n";
        return;
    }
    Instruction* DI = result.first;
    unsigned OPidx = result.second;
    DI->setOperand(OPidx, tI);
    std::string ID = getUID(DI).str();
    ID = ID + ".OP" + std::to_string(OPidx);
    errs()<<"opreplaced "<< ID << "," << tI->getName() << "\n";
}


// Customized dominate analysis
bool dominates(Value* defV, Instruction *I)
{
    if (!defV || !I)
        return false;
    
    if (isa<GlobalValue>(defV) || isa<Constant>(defV))
        return true;

    Function *F = I->getFunction();
    if (dyn_cast_or_null<Argument>(defV)) {
        for (auto &A : F->args()){
            if (&A == defV)
                return true;
        }
        return false;
    }

    DominatorTree DT = DominatorTree(*F);
    if (dyn_cast_or_null<Instruction>(defV))
        if (DT.dominates(cast<Instruction>(defV), I))
            return true;

    return false;
}

// Replace the operands of Instruction I with in-scope values of the
// same type.  If the operands are already in scope, then retain them.
void replaceUnfulfillOperands(Instruction *I){
    if(isa<BranchInst>(I)) return;

    // loop through operands,
    for (auto &op : I->operands()) {
        if (dominates(op.get(), I))
            continue;

        std::pair<Value*, StringRef> ret = randValueBeforeI(I->getFunction(), I, op.get());
        Value *val = ret.first;

        if(val != 0) {
            std::string ID = getUID(I).str();
            ID = ID + ".OP" + std::to_string(op.getOperandNo());
            errs()<<"opreplaced "<< ID << "," << ret.second << "\n";
            I->setOperand(op.getOperandNo(), val);
        }
    }
}

bool iterInstComb(std::fstream &listf, Instruction *SIclone, Instruction *SI, unsigned idx, std::string cumulatedStr) {
    if (idx < SIclone->getNumOperands()) { // iterate through operand
        Value *oprdFrom = SIclone->getOperand(idx);
        if (dominates(oprdFrom, SIclone))
            return iterInstComb(listf, SIclone, SI, idx+1, cumulatedStr);
        else {
            std::vector<std::pair<Value*, StringRef>> resultVec;
            CollectValueBeforeI(SIclone->getFunction(), SIclone, oprdFrom, resultVec);
            if (resultVec.empty())
                return false;
            for (std::pair<Value*, StringRef> metaV : resultVec) {
                std::string next = ", ('-p', '" + getUID(SIclone).str() + ".OP" + std::to_string(idx);
                next = next + "," + metaV.second.str() + "')";
                if (iterInstComb(listf, SIclone, SI, idx+1, cumulatedStr + next) == false)
                    return false;
            }
            return true;
        }
    }
    else if (idx == SIclone->getNumOperands()){ // go for useResult iteration
        if (SI->use_empty()) {
            listf << cumulatedStr << "]\n";
            return true;
        }
        else {
            // std::vector<std::pair<Instruction*, unsigned>> OPvec;
            // CollectOperandAfterI(*SIclone->getFunction(), SIclone, SIclone->getType(), OPvec);
            // if (OPvec.empty())
            //     return true; // not print anything
            // for (std::pair<Instruction*, unsigned> metaOp : OPvec) {
            //     unsigned OPidx = metaOp.second;
            //     std::string next = ", ('-p', '" + getUID(metaOp.first).str() + ".OP" + std::to_string(OPidx);
            //     next = next + "," + getUID(SIclone).str() + "')]\n";
            //     listf << cumulatedStr << next;
            // }

            // we only use the result for the next immediate insturction to reduce mutation duplication.
            Instruction *nextI = SIclone->getNextNonDebugInstruction();
            if (!nextI)
                return false;
            if (nextI->getName().find("nop") != StringRef::npos)
                return false;

            for (auto &oprd : nextI->operands()) {
                if (oprd.get()->getType() == SIclone->getType()) {
                    unsigned OPidx = oprd.getOperandNo();
                    std::string next = ", ('-p', '" + getUID(nextI).str() + ".OP" + std::to_string(OPidx);
                    next = next + "," + getUID(SIclone).str() + "')]\n";
                    listf << cumulatedStr << next;
                }
            }
            return true;
        }
    }
    else {
        assert(0);
    }
}

/***
 * Update I_in's uniqueID metadata. The uniqueID has a foramt like
 * <Originated Inst UID>.<Mode><instance index>. This function is to address
 * how many instruction instance from this I_in's accesstor has existed
 * in the program, and update I_in's instance number accordingly.
 **/
void updateMetadata(Instruction *I_in, std::string mode)
{
  std::string targetMD = getUID(I_in).str();
  targetMD += "." + mode;

  unsigned cnt = 0;
  Module *M = I_in->getModule();
  for(Function &F : *M) {
    for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
    //   if (&*I == I_in)
    //     continue;
      StringRef I_MD = getUID(&*I);
      if (I_MD.find(targetMD) != StringRef::npos)
        cnt++;
    }
  }
  targetMD += std::to_string(cnt+1);
  if (!I_in->getType()->isVoidTy())
    I_in->setName(targetMD);
  setUID(I_in, targetMD);
}

/***
 * This function insert a floated add instruction as a nop.
 * The main usage of this nop instruction is like an anchor,
 * pointing out the position of one instruction before the
 * instruction get cut, replaced, or swapped.
 **/
Instruction* insertNOP(Instruction *I) {
  assert(I->getParent());

  std::string MD = getUID(I).str();
  MD += ".d";

  Value* zero = ConstantInt::get(Type::getInt8Ty(I->getContext()), 0);
  Instruction *nop = BinaryOperator::Create(Instruction::Add, zero, zero, "nop", &*I);
  setUID(nop, MD);

  return nop;
}

//TODO: for each kind of instructions, find a way to play with it.
bool isValidTarget(Instruction *I)
{
    // avoid implicit nop instruction (%nop = add ...)
    if (I->getName().find("nop") != StringRef::npos)
        return false;
    if (isa<CallInst>(I)) {
        CallInst* calI = cast<CallInst>(I);
        if (calI->isIndirectCall())
            // avoid indirect call
            return false;
        if (isa<InlineAsm>(calI->getCalledOperand()))
            // Todo: find a better way to identify a inline assembly
            return true;
        Function *F = calI->getCalledFunction();
        //avoid touching debuging call
        if (F->getName().find("llvm.dbg") != StringRef::npos)
            return false;
    }
    if (isa<BranchInst>(I))
        return false;
    if (isa<PHINode>(I))
        return false;
    if (isa<ReturnInst>(I))
        return false;

    return true;
}

/**
 * This function return the same type of instruction where the inst_desc demand.
 * Since the demand does not require accurate location, only target instruction,
 * It will return any instruction in the same instruction family that inst_desc describes.
 * For example, if the inst_desc is an UID as U14.i1.r1, the
 * function can return any instruction that has UID with U14 since they are
 * in the same instructions family.
 **/
Instruction* walkCollect(StringRef inst_desc, std::string &UID, Module &M)
{
    unsigned count = 0;
    for(Function &F: M) {
    for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
        if (isValidTarget(&*I) == false)
            continue;

        count += 1;
        if (inst_desc[0] != 'U') { // number
            if (count == std::stoul(inst_desc.str())) {
                UID = getUID(&*I).str();
                return &*I;
            }
        }
        else { // unique ID
            StringRef ID = getUID(&*I);
            if (ID.find(".d") != StringRef::npos) continue; // Cannot be a deleted instruction

            StringRef IDBase = ID.split('.').first;
            StringRef targetBase = inst_desc.split('.').first;
            if (IDBase.equals(targetBase)) {
                UID = inst_desc.str();
                return &*I;
            }
        }
    }
    }
    return NULL;
}

/**
 * This function return the instruction that fits inst_desc.
 * Allow to return the nop if the target instruction has been deleted.
 **/
Instruction* walkPosition(std::string inst_desc, std::string &UID, Module &M)
{
    unsigned count = 0;
    for(Function &F: M) {
    for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
        if (isValidTarget(&*I) == false)
            continue;

        count += 1;
        if (inst_desc[0] != 'U') { // number
            if (count == std::stoul(inst_desc)) {
                UID = getUID(&*I).str();
                return &*I;
            }
        }
        else { // unique ID
            std::string ID = getUID(&*I).str();
            if ((ID.compare(inst_desc) == 0) ||
                (ID.compare(inst_desc + ".d") == 0)  ) {
                UID = inst_desc;
                return &*I;
            }
        }
    }
    }
    return NULL;
}

/**
 * This function return the instruction that fits inst_desc exactly.
 **/
Value* walkExact(std::string inst_desc, std::string &UID, Module &M, Type* refT, bool validonly)
{
    unsigned count = 0;
    for(Function &F: M) {
        if (inst_desc[0] == 'A') {
            for (Argument &A : F.args()) {
                if (A.getName() == inst_desc) {
                    UID = inst_desc;
                    return &A;
                }
            }
        }
        else if (inst_desc[0] == 'C') {// Constant. Need to create one
            if (refT == NULL)
                return NULL;
            UID = inst_desc;
            return getConstantValue(refT);
        }
        else { // For instruction
            for (Instruction &I : instructions(F)) {
                if (isValidTarget(&I) == false && validonly == true)
                    continue;

                count += 1;
                if (inst_desc[0] == 'U') { // unique ID
                    std::string ID = getUID(&I).str();
                    if ((inst_desc.compare(ID) == 0)) {
                        UID = inst_desc;
                        return &I;
                    }
                }
                else { // number
                    if (count == std::stoul(inst_desc)) {
                        UID = getUID(&I).str();
                        return &I;
                    }
                }
            }
        }
    }
    return NULL;
}

int replaceOperands(StringRef dst_desc, StringRef src_desc, Module &M)
{
    std::string dummy;
    // decompose destination description into inst and operand
    StringRef dstInstBase = (StringRef(dst_desc)).rsplit('.').first;
    StringRef dstOP = (StringRef(dst_desc)).rsplit('.').second;
    assert(dstOP.find("OP") != StringRef::npos && "Not a valid operand description!");
    unsigned OPindex = std::stoi(dstOP.drop_front(2).str());// remove "OP"
    Instruction *DI = dyn_cast_or_null<Instruction>(walkExact(dstInstBase.str(), dummy, M, NULL, false));
    if (DI == NULL)
        return -1;
    if (OPindex >= DI->getNumOperands())
        return -2;
    Value *DV = DI->getOperand(OPindex);

    Value *SV;
    if (src_desc[0] == 'U' || src_desc[0] == 'A') {
        SV = cast<Value>(walkExact(src_desc.str(), dummy, M, DV->getType(), false));
        if (SV->getType()->isVoidTy())
            return -3;
        if (DV->getType() != SV->getType())
            return -4;
        if (DV == SV)
            return -5;
    }
    else // Constant value
        SV = getConstantValue(DV->getType());

    DI->setOperand(OPindex, SV);
    errs()<<"opreplaced "<< dst_desc << "," << src_desc << "\n";
    return 0;
}

void replaceAllUsesWithReport(Instruction* I, std::pair<Value*, StringRef> metaV)
{
/* Cannot use any iterator based loop since it is changing during the replacing.
   Refer to the code in LLVM:Value::doRAUW. However, since Value::useList is
   a private variable, we need to build the useList by our own first
*/
    std::vector<Use*> useList;
    for(Use &U : I->uses())
        useList.push_back(&U);

    while(!useList.empty()) {
        Use *U = useList.back();
        Instruction *UI = cast<Instruction>(U->getUser());

        std::string ID = getUID(UI).str();
        ID = ID + ".OP" + std::to_string(U->getOperandNo());
        errs()<<"opreplaced "<< ID << "," << metaV.second << "\n";
        U->set(metaV.first);
        useList.pop_back();
    }
}

// declare i32 @llvm.nvvm.ldg.global.i.i32.p0i32(i32* nocapture, i32)
Function *ldgGen(Module &M, Type *inT, Type *outT)
{
    std::string ldgName;
    if (outT == Type::getInt32Ty(M.getContext()))
        ldgName = ldgPre + ".i.i32";
    else if (outT == Type::getInt8Ty(M.getContext()))
        ldgName = ldgPre + ".i.i8";
    else if (outT == Type::getInt64Ty(M.getContext()))
        ldgName = ldgPre + ".i.i64";
    else if (outT == Type::getFloatTy(M.getContext()))
        ldgName = ldgPre + ".f.f32";
    else if (outT == Type::getDoubleTy(M.getContext()))
        ldgName = ldgPre + ".f.f64";
    else
        assert(0);

    if (inT == Type::getInt32PtrTy(M.getContext()))
        ldgName = ldgName + ".p0i32";
    else if (inT == Type::getInt8PtrTy(M.getContext()))
        ldgName = ldgName + ".p0i8";
    else if (inT == Type::getInt64PtrTy(M.getContext()))
        ldgName = ldgName + ".p0i64";
    else if (inT == Type::getFloatPtrTy(M.getContext()))
        ldgName = ldgName + ".p0f32";
    else if (inT == Type::getDoublePtrTy(M.getContext()))
        ldgName = ldgName + ".p0f64";
    else
        assert(0);

    Function *ldgFun = M.getFunction(ldgName);
    if (ldgFun != NULL)
        return ldgFun;

    std::vector<Type*> ldgArgs;
    ldgArgs.push_back(inT);
    ldgArgs.push_back(Type::getInt32Ty(M.getContext()));
    FunctionType *FT =
        FunctionType::get(outT, ldgArgs, false);

    ldgFun =
        Function::Create(FT, Function::ExternalLinkage, ldgName, M);

    return ldgFun;
}

// "ld.global.cg.u32 $0, [$1]", "=r,l"(i32* %U31)
InlineAsm *ldcgGen(Module &M, Type *inT, Type *outT)
{
    std::string asmStr = "ld.global.cg.";
    std::string cStr = "=";
    // TODO: Figure out when to translate to signed int
    if (outT == Type::getInt32Ty(M.getContext()))
    {   asmStr = asmStr + "u32"; cStr = cStr + "r"; }
    else if (outT == Type::getInt8Ty(M.getContext()))
    {   asmStr = asmStr + "u8";  cStr = cStr + "h"; }
    else if (outT == Type::getInt64Ty(M.getContext()))
    {   asmStr = asmStr + "u64"; cStr = cStr + "l"; }
    else if (outT == Type::getFloatTy(M.getContext()))
    {   asmStr = asmStr + "f32"; cStr = cStr + "f"; }
    else if (outT == Type::getDoubleTy(M.getContext()))
    {   asmStr = asmStr + "f64"; cStr = cStr + "d"; }
    else
        assert(0);
    asmStr = asmStr + " $0, [$1];";

    // input can only be a pointer, thus use l constraint
    // for the asm input
    cStr = cStr + ",l";

    std::vector<Type*> ldcgArgs;
    ldcgArgs.push_back(inT);
    FunctionType *FT =
        FunctionType::get(outT, ldcgArgs, false);

    return InlineAsm::get(
        FT,
        asmStr,
        cStr,
        false,
        false,
        llvm::InlineAsm::AD_ATT
    );
}

unsigned int getAlignFromType(Module &M, Type *T)
{
    if (T == Type::getInt32PtrTy(M.getContext()))
        return 4;
    else if (T == Type::getInt8PtrTy(M.getContext()))
        return 1;
    else if (T == Type::getInt64PtrTy(M.getContext()))
        return 8;
    else if (T == Type::getFloatPtrTy(M.getContext()))
        return 4;
    else if (T == Type::getDoublePtrTy(M.getContext()))
        return 8;
    else
        assert(0);
}