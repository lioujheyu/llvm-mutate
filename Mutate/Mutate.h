#include <stdio.h>
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

using namespace llvm;

// Use the result of instruction I somewhere in the basic block in
// which it is defined.  Ideally in the immediately subsequent
// instruction.
void useResult(Instruction *I){
  // we don't care if already used, use it again!
  // if(!I->use_empty()){ errs()<<"already used!\n" };
  BasicBlock *B = I->getParent();
  for (Instruction &i : *B) {
    Instruction *Inst = &i;
    int counter = -1;
    for (User::op_iterator i = I->op_begin(), e = I->op_end(); i != e; ++i){
      counter++;
      Value *v = *i;
      if (v->getType() == I->getType()){
        Inst->setOperand(counter, I);
        return; } } }
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
  // pulled from getNullValue
  switch (T->getTypeID()) {
  case Type::IntegerTyID:
  case Type::HalfTyID:
  case Type::FloatTyID:
  case Type::DoubleTyID:
  case Type::X86_FP80TyID:
  case Type::FP128TyID:
  case Type::PPC_FP128TyID:
  case Type::PointerTyID:
  case Type::StructTyID:
  case Type::ArrayTyID:
  case Type::VectorTyID:
    return Constant::getNullValue(T);
  default:
    return 0;
  }
}

// Replace the operands of Instruction I with in-scope values of the
// same type.  If the operands are already in scope, then retain them.
void replaceOperands(Instruction *I){
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
          Value *val = findInstanceOfType(I, v->getType());
          if(val != 0){
            errs() << "replacing argument: " << v->getName() << "\n";
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

Instruction* walkCollect(unsigned idx, std::string &desc, Module &M)
{
    unsigned count = 0;
    for(Function &F: M) {
    for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
        if (I->getName().compare("nop") == 0)
            continue;
        count += 1;
        if (idx != 0) {
            if (count == idx) {
                MDNode* N = I->getMetadata("uniqueID");
                desc = cast<MDString>(N->getOperand(0))->getString();
                return &*I;
            }
        }
        else {
            MDNode* N = I->getMetadata("uniqueID");
            std::string ID = cast<MDString>(N->getOperand(0))->getString();
            if (desc.compare(ID) == 0)
                return &*I;
        }
    }
    }
    return NULL;
}