#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace {
struct NotEvenPass : public BasicBlockPass {
  static char ID;
  NotEvenPass() : BasicBlockPass(ID) {}

  StringRef extractAnnotationName(ConstantExpr *ce)
  {
    if(ce && ce->getOpcode() == Instruction::GetElementPtr)
    {
      if(GlobalVariable *annoteStr =
          dyn_cast<GlobalVariable>(ce->getOperand(0)))
      {
        if (ConstantDataSequential *data =
            dyn_cast<ConstantDataSequential>(
                annoteStr->getInitializer())) {
          if (data->isString()) {
            return data->getAsCString();
          }
        }
      }
    }
    return "";
  }

  bool runOnBasicBlock(BasicBlock &BB) override {
    auto assume = BB.getParent()->getParent()->getOrInsertFunction(
        "__assume__", Type::getVoidTy(BB.getContext()),
        Type::getInt1Ty(BB.getContext()));

    // Run over each Instruction in the BB
    Value *two = ConstantInt::getSigned(Type::getInt8Ty(BB.getContext()), 2);
    Value *zero = ConstantInt::getSigned(Type::getInt8Ty(BB.getContext()), 0);
    for(Instruction &I : BB)
    {
      // Check if it is a CallInstruction
      if(I.getOpcode() == Instruction::Call) {
        auto callInst = cast<CallInst>(&I);
        auto calledFunction = callInst->getCalledFunction();
        StringRef name("");
        if(callInst->getOperand(1)->getValueID() == Value::ConstantExprVal)
        {
          ConstantExpr *ce =
              // Second Argument is the Annotation Name
              cast<ConstantExpr>(callInst->getOperand(1));
          name = extractAnnotationName(ce);
        }

          if(name.equals("not_even"))
          {
            IRBuilder<> builder(reinterpret_cast<Instruction*>(&I));

            Value *load = builder.CreateLoad(callInst->getOperand(0));
            // %Var MOD 2
            Value* srem = builder.CreateSRem(load, two);
            // (var MOD 2) != 0
            Value* cmp = builder.CreateICmp(CmpInst::ICMP_NE, srem, zero);

            builder.CreateCall(assume, cmp);
          }

      }
    }
    return true;
  }
}; // end of struct NotEvenPass
}  // end of anonymous namespace

char NotEvenPass::ID = 0;
static RegisterPass<NotEvenPass> X("not_even", "Not Even Pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);