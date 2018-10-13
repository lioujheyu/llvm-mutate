#include <stdio.h>
#include <cstdlib>
#include <ctime>
#include <random>
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

using namespace llvm;

std::random_device rd;
std::mt19937 gen(rd());

Value* getConstantValue(Type* T)
{
    switch(T->getTypeID()) {
    case Type::IntegerTyID: case Type::VectorTyID:
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

void CollectValueBeforeI(BasicBlock &BB, Instruction* boundary, Value* refOP,
                           std::vector<std::pair<Value*, StringRef>> &resultVec)
{
    Type *T = (refOP != NULL)? refOP->getType() : NULL;
    for (Argument &A : BB.getParent()->args()) {
        if (T != NULL) {
            if (A.getType() != T)
                continue;
        }
        resultVec.push_back(std::make_pair(&A, A.getName()));
    }
    for (Instruction &I : BB) {
        if (&I == boundary)
            break;
        if (&I == refOP)
            continue;
        if (I.getType()->isVoidTy())
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
    for (Function &F : M)
        for (BasicBlock &BB : F)
            CollectValueBeforeI(BB, NULL, NULL, resultVec);

    std::uniform_int_distribution<> randIdx(0, resultVec.size()-1);
    return resultVec[randIdx(gen)];
}

std::pair<Value*, StringRef> randValueBeforeI(BasicBlock &BB, Instruction* boundary, Value* refOP)
{
    std::vector<std::pair<Value*, StringRef>> resultVec;
    CollectValueBeforeI(BB, boundary, refOP, resultVec);
    // has constant to participate in drawing
    resultVec.push_back(std::make_pair(getConstantValue(refOP->getType()), StringRef("C")));

    std::uniform_int_distribution<> randIdx(0, resultVec.size()-1);
    return resultVec[randIdx(gen)];
}

std::pair<Instruction*, unsigned> randOperandAfterI(Function &F, Instruction* boundary, Type* T)
{
    std::vector<std::pair<Instruction*, unsigned>> OPvec;
    if (boundary == NULL) { // Get the all from the function
        for (Instruction &I : instructions(F)) {
            for (unsigned i=0; i<I.getNumOperands(); i++) {
                Value *op = I.getOperand(i);
                if (T == NULL)
                    OPvec.push_back(std::make_pair(&I, i));
                else if (op->getType() == T)
                    OPvec.push_back(std::make_pair(&I, i));
            }
        }
    }
    else{ // has a boundary. Limit the search space to the basic block
        BasicBlock *BB = boundary->getParent();
        BasicBlock::iterator I;
        for (I=BB->begin(); I!=BB->end(); ++I) {
            if (boundary == &*I)
                break;
        }
        I++;
        for (I; I!=BB->end(); ++I) {
            for (unsigned i=0; i<I->getNumOperands(); i++) {
                Value *op = I->getOperand(i);
                if (T == NULL)
                    OPvec.push_back(std::make_pair(&*I, i));
                else if (op->getType() == T)
                    OPvec.push_back(std::make_pair(&*I, i));
            }
        }
    }

    Instruction* dummy = NULL;
    if (OPvec.empty())
        return std::make_pair(dummy, 0);

    std::uniform_int_distribution<> randIdx(0, OPvec.size()-1);
    return OPvec[randIdx(gen)];
}

// Use the result of instruction tI somewhere in the basic block in
// which it is defined.  Ideally in the immediately subsequent
// instruction.
void useResult(Instruction *tI){
  // we don't care if already used, use it again!
  // if(!I->use_empty()){ errs()<<"already used!\n" };
    BasicBlock *BB = tI->getParent();
    BasicBlock::iterator I;
    for (I=BB->begin(); I!=BB->end(); ++I) {
        if (tI == &*I)
            break;
    }
    I++;
    for (I; I!=BB->end(); ++I) {
        int counter = -1;
        for (User::op_iterator Iop = I->op_begin(), e = I->op_end(); Iop != e; ++Iop){
            counter++;
            Value *v = *Iop;
            if (v->getType() == tI->getType()){
                I->setOperand(counter, tI);
                // MDNode* N = I->getMetadata("uniqueID");
                // std::string ID = cast<MDString>(N->getOperand(0))->getString();
                // ID = ID + ".OP" + std::to_string(counter);
                // errs()<<"opreplaced "<< ID << "," << tI->getName() << "\n";
                return;
            }
        }
    }
    errs()<<"could find no use for result\n";
}

// Find a value of Type T which can be used at Instruction I.  Search
// in this order.
// 1. values in Basic Block before I
// 2. arguments to the function containing I
// 3. global values
// 4. null of the correct type
// 5. return a 0 that the caller can stick where the sun don't shine
Value *findInstanceOfType(Instruction *I, Type *T){
  bool isPointer = I->getType()->isPointerTy();

  // local inside the Basic Block
  BasicBlock *B = I->getParent();
  for (BasicBlock::iterator prev = B->begin(); cast<Value>(prev) != I; ++prev){
    if((isPointer && prev->getType()->isPointerTy()) ||
       (prev->getType() == T)){
      errs()<<"found local replacement: "<<cast<Value>(prev)<<"\n";
      return cast<Value>(prev); } }

  // arguments to the function
  Function *F = B->getParent();
  for (Function::arg_iterator arg = F->arg_begin(), E = F->arg_end();
       arg != E; ++arg){
    if((isPointer && arg->getType()->isPointerTy()) ||
       (arg->getType() == T)){
      errs()<<"found arg replacement: "<<arg<<"\n";
      return cast<Value>(arg); } }

  // global values
  Module *M = F->getParent();
  for (Module::global_iterator g = M->global_begin(), E = M->global_end();
       g != E; ++g){
    if((isPointer && g->getType()->isPointerTy()) ||
       (g->getType() == T)){
      errs()<<"found global replacement: "<<cast<Value>(g)<<"\n";
      return cast<Value>(g); } }

  // TODO: types which could be replaced with sane default
  //       - result of comparisons
  //       - nulls or zeros for number types
  //         (This is questionable. Why use zero instead of one?)
  // pulled from getNullValue
  return getConstantValue(T);
}

// Replace the operands of Instruction I with in-scope values of the
// same type.  If the operands are already in scope, then retain them.
void replaceUnfulfillOperands(Instruction *I){
  // don't touch arguments of branch instructions
  if(isa<BranchInst>(I)) return;

  // loop through operands,
  int counter = -1;
  for (User::op_iterator i = I->op_begin(), e = I->op_end(); i != e; ++i) {
    counter++;
    Value *v = *i;

    // don't touch global or constant values
    if (!isa<GlobalValue>(v) && !isa<Constant>(v)){

      // don't touch arguments to the current function
      Function *F = I->getParent()->getParent();
      bool isAnArgument = false;
      for (Function::arg_iterator arg = F->arg_begin(), E = F->arg_end();
           arg != E; ++arg) {
        if( arg == v ){ isAnArgument = true; break; } }

      if(!isAnArgument) {
        // Don't touch operands which are in scope
        BasicBlock *B = I->getParent();
        bool isInScope = false;
        for (BasicBlock::iterator i = B->begin();
             cast<Instruction>(i) != I; ++i)
          if(&*i == v) { isInScope = true; break; }

        if(!isInScope){
          // If we've made it this far we really do have to find a replacement
          std::pair<Value*, StringRef> ret = randValueBeforeI(*(I->getParent()), I, v);
          Value *val = ret.first;

        //   Value *val = findInstanceOfType(I, v->getType());
          if(val != 0){
            MDNode* N = I->getMetadata("uniqueID");
            std::string ID = cast<MDString>(N->getOperand(0))->getString();
            ID = ID + ".OP" + std::to_string(counter);
            errs()<<"opreplaced "<< ID << "," << ret.second << "\n";
            I->setOperand(counter, val); } } } } }
}

/***
 * Update I_in's uniqueID metadata. The uniqueID has a foramt like
 * <Originated Inst UID>.<Mode><instance index>. This function is to address
 * how many instruction instance from this I_in's accesstor has existed
 * in the program, and update I_in's instance number accordingly.
 **/
void updateMetadata(Instruction *I_in, std::string mode)
{
  MDNode* N = I_in->getMetadata("uniqueID");
  std::string targetMD = cast<MDString>(N->getOperand(0))->getString();
  targetMD += "." + mode;

  unsigned cnt = 0;
  Module *M = I_in->getModule();
  for(Function &F : *M) {
    for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
      MDNode* N = I->getMetadata("uniqueID");
      StringRef I_MD = cast<MDString>(N->getOperand(0))->getString();
      if (I_MD.find(targetMD) != StringRef::npos)
        cnt++;
    }
  }
  targetMD += std::to_string(cnt+1);
  if (!I_in->getType()->isVoidTy())
    I_in->setName(targetMD);
  LLVMContext& C = I_in->getContext();
  N = MDNode::get(C, MDString::get(C, targetMD));
  I_in->setMetadata("uniqueID", N);
}

/***
 * This function insert a floated add instruction as a nop.
 * The main usage of this nop instruction is like an anchor,
 * pointing out the position of one instruction before the
 * instruction get cut, replaced, or swapped.
 **/
Instruction* insertNOP(Instruction *I) {
  assert(I->getParent());

  MDNode* N = I->getMetadata("uniqueID");
  std::string MD = cast<MDString>(N->getOperand(0))->getString();
  MD += ".d";

  Value* zero = ConstantInt::get(Type::getInt8Ty(I->getContext()), 0);
  Instruction *nop = BinaryOperator::Create(Instruction::Add, zero, zero, "nop", &*I);

  LLVMContext& C = nop->getContext();
  MDNode* Nnop = MDNode::get(C, MDString::get(C, MD));
  nop->setMetadata("uniqueID", Nnop);

  return nop;
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
        if (I->getName().find("nop") != StringRef::npos)
            continue;
        count += 1;
        if (inst_desc[0] != 'U') { // number
            if (count == std::stoul(inst_desc)) {
                MDNode* N = I->getMetadata("uniqueID");
                UID = cast<MDString>(N->getOperand(0))->getString();
                return &*I;
            }
        }
        else { // unique ID
            MDNode* N = I->getMetadata("uniqueID");
            StringRef ID = cast<MDString>(N->getOperand(0))->getString();
            if (ID.find(".d") != StringRef::npos) continue; // Cannot be a deleted instruction

            StringRef IDBase = ID.split('.').first;
            StringRef targetBase = inst_desc.split('.').first;
            if (IDBase.equals(targetBase)) {
                UID = inst_desc;
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
        if (I->getName().find("nop") != StringRef::npos)
            continue;
        count += 1;
        if (inst_desc[0] != 'U') { // number
            if (count == std::stoul(inst_desc)) {
                MDNode* N = I->getMetadata("uniqueID");
                UID = cast<MDString>(N->getOperand(0))->getString();
                return &*I;
            }
        }
        else { // unique ID
            MDNode* N = I->getMetadata("uniqueID");
            std::string ID = cast<MDString>(N->getOperand(0))->getString();
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
Value* walkExact(std::string inst_desc, std::string &UID, Module &M, Type* refT)
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
                if (I.getName().find("nop") != StringRef::npos)
                    continue;
                count += 1;
                if (inst_desc[0] == 'U') { // unique ID
                    MDNode* N = I.getMetadata("uniqueID");
                    std::string ID = cast<MDString>(N->getOperand(0))->getString();
                    if ((inst_desc.compare(ID) == 0)) {
                        UID = inst_desc;
                        return &I;
                    }
                }
                else { // number
                    if (count == std::stoul(inst_desc)) {
                        MDNode* N = I.getMetadata("uniqueID");
                        UID = cast<MDString>(N->getOperand(0))->getString();
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
    unsigned OPindex = std::stoi(dstOP.drop_front(2));// remove "OP"
    Instruction *DI = cast<Instruction>(walkExact(dstInstBase, dummy, M, NULL));
    if (DI == NULL)
        return -1;
    if (OPindex >= DI->getNumOperands())
        return -2;
    Value *DV = DI->getOperand(OPindex);

    Value *SV;
    if (src_desc[0] == 'U' || src_desc[0] == 'A') {
        SV = cast<Value>(walkExact(src_desc, dummy, M, DV->getType()));
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
    for (User *U : I->users()) {
        Instruction *UI = cast<Instruction>(U);
        for (int i=0; i<UI->getNumOperands(); i++) {
            if (UI->getOperand(i) != cast<Value>(I))
                continue;

            UI->setOperand(i, metaV.first);
            MDNode* N = UI->getMetadata("uniqueID");
            std::string ID = cast<MDString>(N->getOperand(0))->getString();
            ID = ID + ".OP" + std::to_string(i);
            errs()<<"opreplaced "<< ID << "," << metaV.second << "\n";
        }
    }
}