// Copyright (C) 2013 Eric Schulte
#include "Mutate.h"

using namespace llvm;

cl::opt<std::string> Inst1("inst1", cl::init("0"), cl::desc("first statement to mutate"));
cl::opt<std::string> Inst1ID("inst1ID", cl::init(""), cl::desc("The Unique ID of first statement to mutate"));

cl::opt<std::string> Inst2("inst2", cl::init("0"), cl::desc("second statement to mutate"));
cl::opt<std::string> Inst2ID("inst2ID", cl::init(""), cl::desc("The Unique ID of first statement to mutate"));

namespace {
  struct Ids : public ModulePass {
    static char ID;
    Ids() : ModulePass(ID) {}

    bool runOnModule(Module &M){
      count = 0;
      for (Module::iterator I = M.begin(), E = M.end(); I != E; ++I)
        walkFunction(&*I);

      errs() << count << "\n";

      return false;
    }

    // We don't modify the program, so we preserve all analyses
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesAll(); }

  private:
    int unsigned count;
    void walkFunction(Function *F){
      for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
        if (I->getName().find("nop") == StringRef::npos)
          count += 1;
      }
    }
  };
}

namespace {
  struct List : public ModulePass {
    static char ID;
    List() : ModulePass(ID) {}

    bool runOnModule(Module &M){
      count = 0;
      for (Module::iterator I = M.begin(), E = M.end(); I != E; ++I)
        walkFunction(&*I);
      return false;
    }

    // We don't modify the program, so we preserve all analyses
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesAll(); }

  private:
    int unsigned count;
    void walkFunction(Function *F){
      for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
        count += 1;
        errs() << count << "\t" << I->getType();
        for (User::op_iterator i = I->op_begin(), e = I->op_end(); i != e; ++i)
          errs() << "\t" << cast<Value>(i)->getType();
        errs() << "\n"; } }
  };
}

namespace {
  struct Name : public ModulePass {
    static char ID;
    Name() : ModulePass(ID) {}

    bool runOnModule(Module &M){
      count = 0;
      for (Module::iterator I = M.begin(), E = M.end(); I != E; ++I)
        walkFunction(&*I);
      return false;
    }

    // We don't modify the program, so we preserve all analyses
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesAll(); }

  private:
    int unsigned count;

    void walkFunction(Function *F){
      for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
        count += 1;
        std::string uniqueID = "U" + std::to_string(count);
        LLVMContext& C = I->getContext();
        MDNode* N = MDNode::get(C, MDString::get(C, uniqueID));
        I->setMetadata("uniqueID", N);
      }
    }
  };
}

namespace {
  struct Trace : public ModulePass {
    static char ID;
    Trace() : ModulePass(ID) {}

    bool runOnModule(Module &M){
      count = 0;
      PutFn = M.getOrInsertFunction("llvm_mutate_trace",
                                    Type::getVoidTy(M.getContext()),
                                    Type::getInt32Ty(M.getContext()));
      for (Module::iterator I = M.begin(), E = M.end(); I != E; ++I)
        walkFunction(&*I);
      return true;
    }

  private:
    int unsigned count;
    Constant *PutFn;
    CallInst *PutCall;

    void walkFunction(Function *F){
      for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
        Instruction *Inst = &*I;
        count += 1;
        // to avoid: PHI nodes not grouped at top of basic block!
        if(!isa<PHINode>(Inst)){
          // turn the count into an argument array of constant integer values
          Value *Args[1];
          Args[0] = ConstantInt::get(Type::getInt32Ty(F->getContext()), count);
          PutCall = CallInst::Create(PutFn, Args, "", Inst);
        }
      }
    }
  };
}

namespace {
  struct Cut : public ModulePass {
    static char ID;
    Cut() : ModulePass(ID) {}

    bool runOnModule(Module &M){
      Instruction *I = walkExact(Inst1, Inst1ID, M);
      if (I == NULL) {
        errs() << "cut failed. Cannot find " << Inst1 << "\n";
        return EXIT_FAILURE; }

      insertNOP(I);
      // decouple the dependence from later instructions
      if(!I->use_empty()){
        Value *Val = findInstanceOfType(I, I->getType());
        if(Val != 0){
          I->replaceAllUsesWith(Val); } }
      // TODO: have a function as a recycle bin to store deleted inst
      I->eraseFromParent();
      errs() << "cut " << Inst1ID << "\n";
      return EXIT_SUCCESS;}
  };
}

namespace {
  struct Insert : public ModulePass {
    static char ID;
    Insert() : ModulePass(ID) {}

    bool runOnModule(Module &M){
      Instruction *temp;
      Instruction *SI = walkCollect(Inst2, Inst2ID, M);
      Function* F;
      if (isa<CallInst>(SI)) { // TODO: copy indirect invocation
        F = cast<CallInst>(SI)->getCalledFunction();
      }
      Instruction *DI = walkPosition(Inst1, Inst1ID, M);
      if (SI == NULL or DI == NULL or F == NULL) {
        errs()<<"insertion failed. Cannot find ";
        if (DI == NULL) errs()<<Inst1 << " ";
        if (SI == NULL) errs()<<Inst2 << " ";
        errs() << "\n";
        return EXIT_FAILURE; }

      temp = SI->clone();
      if (!temp->getType()->isVoidTy())
        temp->setName(SI->getName()+".insert");
      MDNode* N = SI->getMetadata("uniqueID");
      Inst2ID = cast<MDString>(N->getOperand(0))->getString();

      temp->insertBefore(&*DI); // insert temp before DI
      replaceOperands(temp); // wire incoming edges of CFG into temp
      // check if I generates a result which is used, if not then
      // it is probably run for side effects and we don't need to
      // wire the result of the copy of I to something later on
      bool result_ignorable_p = SI->use_empty();
      if(!result_ignorable_p)
        useResult(temp); // wire outgoing results of temp into CFG
      updateMetadata(temp, "i");

      errs()<<"inserted " << Inst1ID << "," << Inst2ID << "\n";
      return EXIT_SUCCESS;
    }
  };
}

namespace {
  struct Replace : public ModulePass {
    static char ID; // pass identification
    Replace() : ModulePass(ID) {}

    bool runOnModule(Module &M){
      Instruction *temp;
      Instruction *SI = walkCollect(Inst2, Inst2ID, M);
      Instruction *DI = walkPosition(Inst1, Inst1ID, M);
      Function* F;
      if (isa<CallInst>(SI)) { // TODO: copy indirect invocation
        F = cast<CallInst>(SI)->getCalledFunction();
      }
      if (SI == NULL or DI == NULL or F == NULL) {
        errs()<<"replace failed. Cannot find ";
        if (DI == NULL) errs()<<Inst1 << " ";
        if (SI == NULL) errs()<<Inst2 << " ";
        errs() << "\n";
        return EXIT_FAILURE; }

      temp = SI->clone();
      if (!temp->getType()->isVoidTy())
        temp->setName(SI->getName()+".replace1");

      insertNOP(&*DI);
      ReplaceInstWithInst(DI, temp);
      replaceOperands(temp);
      updateMetadata(temp, "r");

      errs()<<"replaced "<< Inst1ID << "," << Inst2ID << "\n";
      return EXIT_SUCCESS; }
  };
}

namespace {
  struct Move : public ModulePass {
    static char ID; // pass identification
    Move() : ModulePass(ID) {}

    bool runOnModule(Module &M){
      Instruction *temp;
      Instruction *SI = walkExact(Inst2, Inst2ID, M);
      Instruction *DI = walkPosition(Inst1, Inst1ID, M);
      Function* F;
      if (isa<CallInst>(SI)) { // TODO: copy indirect invocation
        F = cast<CallInst>(SI)->getCalledFunction();
      }
      if (SI == NULL or DI == NULL or F == NULL) {
        errs()<<"Move failed. Cannot find ";
        if (DI == NULL) errs()<<Inst1 << " ";
        if (SI == NULL) errs()<<Inst2 << " ";
        errs() << "\n";
        return EXIT_FAILURE; }

      temp = SI->clone();
      if (!temp->getType()->isVoidTy())
        temp->setName(SI->getName()+".move");
      MDNode* N = SI->getMetadata("uniqueID");
      Inst2ID = cast<MDString>(N->getOperand(0))->getString();

      temp->insertBefore(&*DI); // insert temp before DI
      replaceOperands(temp);
      bool result_ignorable_p = SI->use_empty();
      if(!result_ignorable_p)
        useResult(temp);
      // Delete the source instruction if it is there
      insertNOP(SI);
      if(!SI->use_empty()){
        Value *Val = findInstanceOfType(SI, SI->getType());
        if(Val != 0){
          SI->replaceAllUsesWith(Val); } }
      // TODO: have a function as a recycle bin to store deleted inst
      SI->eraseFromParent();
      updateMetadata(temp, "m");

      errs()<<"moved " << Inst1ID << "," << Inst2ID << "\n";
      return EXIT_SUCCESS; }
  };
}

namespace {
  struct Swap : public ModulePass {
    static char ID; // pass identification
    Swap() : ModulePass(ID) {}

    bool runOnModule(Module &M){
      Instruction *temp1, *temp2;
      Instruction *I1 = walkExact(Inst1, Inst1ID, M);
      Instruction *I2 = walkExact(Inst2, Inst2ID, M);
      Function *F1, *F2;
      if (isa<CallInst>(I1)) { // TODO: copy indirect invocation
        F1 = cast<CallInst>(I1)->getCalledFunction();
      }
      if (isa<CallInst>(I2)) { // TODO: copy indirect invocation
        F2 = cast<CallInst>(I2)->getCalledFunction();
      }
      if (I1 == NULL or I2 == NULL or F1 == NULL or F2 == NULL) {
        errs()<<"swap failed. Cannot find ";
        if (I1 == NULL) errs()<<Inst1 << " ";
        if (I2 == NULL) errs()<<Inst2 << " ";
        errs() << "\n";
        return EXIT_FAILURE; }

      temp1 = I1->clone();
      if (!temp1->getType()->isVoidTy())
        temp1->setName(I1->getName()+".swap1");
      temp2 = I2->clone();
      if (!temp2->getType()->isVoidTy())
        temp2->setName(I2->getName()+".swap2");

      // confirm that the types match
      if(temp1->getType() != temp2->getType()) {
        errs() << "type mismatch " <<
          temp1->getType() << " and " <<
          temp2->getType() << "\n";
        temp1->deleteValue();
        temp2->deleteValue();
        return EXIT_FAILURE; }

      insertNOP(&*I1);
      insertNOP(&*I2);
      ReplaceInstWithInst(I2, temp1);
      replaceOperands(temp1);
      updateMetadata(temp1, "s");
      ReplaceInstWithInst(I1, temp2);
      replaceOperands(temp2);
      updateMetadata(temp2, "s");

      errs()<<"swapped " << Inst1ID << "," << Inst2ID << "\n";

      return EXIT_SUCCESS; }
  };
}

char Ids::ID = 0;
char List::ID = 0;
char Name::ID = 0;
char Trace::ID = 0;
char Cut::ID = 0;
char Insert::ID = 0;
char Move::ID = 0;
char Replace::ID = 0;
char Swap::ID = 0;
static RegisterPass<Ids>     S("ids",     "print the number of instructions");
static RegisterPass<List>    T("list",    "list instruction's type and id");
static RegisterPass<Name>    U("name",    "name each instruction by its id");
static RegisterPass<Trace>   V("trace",   "instrument to print inst. trace");
static RegisterPass<Cut>     W("cut",     "cut instruction number inst1");
static RegisterPass<Insert>  X("insert",  "insert inst2 before inst1");
static RegisterPass<Replace> Y("replace", "replace inst1 with inst2");
static RegisterPass<Move>    ZA("move",    "move inst2 before inst1");
static RegisterPass<Swap>    Z("swap",    "swap inst1 and inst2");