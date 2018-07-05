#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Transforms/AnnotationsInference.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Module.h"
#include "z3++.h"
#include "llvm/IR/Instructions.h"
#include <fstream>
#include <map>
#include "z3.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/IR/Constants.h"
using namespace llvm;

#define SKIP_DEBUG(x) 
static cl::opt<std::string> lfFileName("lf-filename", cl::init(""));

namespace {
	struct AnnotationsInference : public FunctionPass {
		static char ID;

		AnnotationsInference() : FunctionPass(ID) {
			initializeAnnotationsInferencePass(*PassRegistry::getPassRegistry());
		}
		void insert_implies(std::string LHS, std::string RHS, int LHS_depth, int RHS_depth, std::map<std::string, z3::expr> &variables, std::map<std::string, int> &variables_depth, z3::solver &func_solver) {
			std::string LHS_name = LHS;
			std::string RHS_name = RHS;
			for (int i = 0; i < LHS_depth; i++) {
				LHS_name = LHS_name + "$p";
			}
			for (int i = 0; i < RHS_depth; i++) {
				RHS_name = RHS_name + "$p";
			}
			//errs() << LHS << " " << RHS << "\n";
			z3::expr condition = implies(variables.find(LHS_name)->second, variables.find(RHS_name)->second);
			func_solver.add(condition);
			//errs() << "Inserted condition : " << LHS_name << " => " << RHS_name << "\n";
			LHS_depth++;
			RHS_depth++;
			while (LHS_depth < variables_depth[LHS] && RHS_depth < variables_depth[RHS]) {
				LHS_name = LHS_name + "$p";
				RHS_name = RHS_name + "$p";
				z3::expr condition = (variables.find(LHS_name)->second == variables.find(RHS_name)->second);
				func_solver.add(condition);
				//errs() << "Inserted condition : " << LHS_name << " == " << RHS_name << "\n";
				LHS_depth++;
				RHS_depth++;
			}
			return;

		}
		void insert_implies_only(std::string LHS, std::string RHS, int LHS_depth, int RHS_depth, std::map<std::string, z3::expr> &variables, std::map<std::string, int> &variables_depth, z3::solver &func_solver) {
			std::string LHS_name = LHS;
			std::string RHS_name = RHS;
			for (int i = 0; i < LHS_depth; i++) {
				LHS_name = LHS_name + "$p";
			}
			for (int i = 0; i < RHS_depth; i++) {
				RHS_name = RHS_name + "$p";
			}
			z3::expr condition = implies(variables.find(LHS_name)->second, variables.find(RHS_name)->second);
			func_solver.add(condition);
			//errs() << "Inserted condition : " << LHS_name << " => " << RHS_name << "\n";
			return;
		}
		Value * opActual(Value* V) {
			if (ConstantExpr *CE = dyn_cast<ConstantExpr>(V)) {
				return opActual(CE->getOperand(0));
			}
			else {
				return V;
			}
		}
		bool isInSpecialHandleList(const Instruction& I) {
			
			const Instruction *Ii = &I;
			const CallInst *CI = dyn_cast<CallInst>(Ii);
			//errs() << "Special list check ";
			//CI->dump();

			Function *TF = CI->getCalledFunction();
			if (TF == NULL) {
				return false;
			}
			else {
				std::string func_name = TF->getName().str();
				if (strncmp(func_name.c_str(), "llvm.", 5) == 0)
					return true;
				return false;
			}
			return false;
		}
		bool runOnFunction(Function &F) override {
			
			//errs() << "Inferring annotations for : " << F.getName() << "\n";
			z3::context func_context;
			z3::solver func_solver(func_context);
			

			z3::expr true_const = func_context.bool_val(true);
			z3::expr false_const = func_context.bool_val(false);
			
			std::map<std::string, z3::expr> variables;
			std::map<std::string, int> variables_depth;


			Module* module = F.getParent();

			Module::FunctionListType& functions = module->getFunctionList();
			for (auto func_var = functions.begin(); func_var != functions.end(); func_var++) {
				std::string var_name = "@" + func_var->getName().str();
				variables.insert(std::pair<std::string, z3::expr>(var_name, func_context.bool_const(var_name.c_str())));
				z3::expr condition = variables.find(var_name)->second == false_const;
				func_solver.add(condition);
				variables_depth[var_name] = 1;
			}

			Module::GlobalListType& globals = module->getGlobalList();
			for (auto glob_var = globals.begin(); glob_var != globals.end(); glob_var++) {
				
				Type *ty = glob_var->getType();
				MDNode *md_node = glob_var->getMetadata("sgx_type");
				int index = 0;
		
				std::string var_name = "@"+glob_var->getName().str();
				int depth = 0;
				while (1) {
					variables.insert(std::pair<std::string, z3::expr>(var_name, func_context.bool_const(var_name.c_str())));
					std::string type;
					if (md_node)
						type = dyn_cast<MDString>(md_node->getOperand(index).get())->getString();
					else
						type = "public";
					index++;
					if (type.compare("public") == 0) {
						z3::expr condition = variables.find(var_name)->second == false_const;
						func_solver.add(condition);
					}
					else {
						z3::expr condition = variables.find(var_name)->second == true_const;
						func_solver.add(condition);
					}
					var_name = var_name + "$p";
					depth++;

					if (!ty->isPointerTy())
						break;
					ty = ty->getPointerElementType();

				}
				variables_depth["@"+glob_var->getName().str()] = depth;
			}
			Type *ty = F.getReturnType();
			std::string var_name = "$result";
			int depth = 1;
			//std::istringstream annotation(function_signatures[F.getName().str()][0]);
			MDNode *md_node = F.getMetadata("sgx_return_type");
			int index = 0;
			while (ty->isPointerTy()) {
				//errs() << "Creating var : " << var_name << "\n";
				variables.insert(std::pair<std::string, z3::expr>(var_name, func_context.bool_const(var_name.c_str())));
				ty = ty->getPointerElementType();
				std::string type;
				type = dyn_cast<MDString>(md_node->getOperand(index).get())->getString();
				index++;
				//errs() << "Type = " << type << "\n";
				if (type.compare("public") == 0) {
					z3::expr condition = variables.find(var_name)->second == false_const;
					func_solver.add(condition);
				}
				else {
					z3::expr condition = variables.find(var_name)->second == true_const;
					func_solver.add(condition);
				}
				var_name = var_name + "$p";
				depth++;
			}
			//errs() << "Creating var : " << var_name << "\n";
			variables.insert(std::pair<std::string, z3::expr>(var_name, func_context.bool_const(var_name.c_str())));
			std::string type;
			type = dyn_cast<MDString>(md_node->getOperand(index).get())->getString();
			//errs() << "Type = " << type << "\n";
			if (type.compare("public") == 0) {
				z3::expr condition = variables.find(var_name)->second == false_const;
				func_solver.add(condition);
			}
			else {
				z3::expr condition = variables.find(var_name)->second == true_const;
				func_solver.add(condition);
			}
			variables_depth["$result"] = depth;



			int arg_order = 0;
			//errs() << F.getName().str() << "\n";
			for (Function::arg_iterator Ai = F.arg_begin(); Ai != F.arg_end(); Ai++) {
				MDNode *md_node = dyn_cast<MDNode>(F.getMetadata("sgx_type")->getOperand(arg_order).get());
				arg_order++;
				Argument &A = *Ai;
				std::string arg_name = A.getName().str();
				Type *ty = A.getType();
				int depth = 1;
				int index = 0;
				while (ty->isPointerTy()) {
					//errs() << "Creating var : " << arg_name << "\n";
					variables.insert(std::pair<std::string, z3::expr>(arg_name, func_context.bool_const(arg_name.c_str())));
					ty = ty->getPointerElementType();
					std::string type;
					type = dyn_cast<MDString>(md_node->getOperand(index).get())->getString();
					index++;
					//errs() << "Type = " << type << "\n";
					if (type.compare("public") == 0) {
						z3::expr condition = variables.find(arg_name)->second == false_const;
						func_solver.add(condition);
					}
					else {
						z3::expr condition = variables.find(arg_name)->second == true_const;
						func_solver.add(condition);
					}
					arg_name = arg_name + "$p";
					depth++;
				}
				//errs() << "Creating var : " << arg_name << "\n";
				variables.insert(std::pair<std::string, z3::expr>(arg_name, func_context.bool_const(arg_name.c_str())));
				std::string type;
				type = dyn_cast<MDString>(md_node->getOperand(index).get())->getString();
				//errs() << "Type = " << type << "\n";
				if (type.compare("public") == 0) {
					z3::expr condition = variables.find(arg_name)->second == false_const;
					func_solver.add(condition);
				}
				else {
					z3::expr condition = variables.find(arg_name)->second == true_const;
					func_solver.add(condition);
				}
				variables_depth[A.getName().str()] = depth;
			}

			for (Function::iterator BBi = F.begin(); BBi != F.end(); BBi++) {
				BasicBlock &BB = *BBi;
				for (BasicBlock::iterator Ii = BB.begin(); Ii != BB.end(); Ii++) {
					Instruction &I = *Ii;
					if (I.getName().str().compare("") != 0) {
						std::string var_name = I.getName().str();
						Type *ty = I.getType();
						int depth = 1;
						while (ty->isPointerTy()) {
							//errs() << "Creating var : " << var_name << "\n";
							variables.insert(std::pair<std::string, z3::expr>(var_name, func_context.bool_const(var_name.c_str())));
							var_name = var_name + "$p";
							ty = ty->getPointerElementType();
							depth++;
						}
						//errs() << "Creating var : " << var_name << "\n";
						variables.insert(std::pair<std::string, z3::expr>(var_name, func_context.bool_const(var_name.c_str())));
						variables_depth[I.getName().str()] = depth;
					}
					
				}
			}
			for (Function::iterator BBi = F.begin(); BBi != F.end(); BBi++) {
				BasicBlock &BB = *BBi;
				for (BasicBlock::iterator Ii = BB.begin(); Ii != BB.end(); Ii++) {
					Instruction &I = *Ii;
					//Ii->dump();
					if (I.getOpcode() == Instruction::Load) {
						std::string var_name = I.getName().str();
						std::string arg_name = opActual(I.getOperand(0))->getName().str();
						if (isa<GlobalObject>(opActual(I.getOperand(0)))) {
							arg_name = "@" + arg_name;
						}
						if (arg_name.compare("")) {
							insert_implies(arg_name, var_name, 1, 0, variables, variables_depth, func_solver);
							insert_implies_only(arg_name, var_name, 0, 0, variables, variables_depth, func_solver);
						}
						else {
							SKIP_DEBUG(errs() << "Skipping ";
							opActual(I.getOperand(0))->dump();)
						}
						
					}
					else if (I.getOpcode() == Instruction::Store) {
						std::string arg1_name = opActual(I.getOperand(0))->getName().str();
						if (isa<GlobalObject>(opActual(I.getOperand(0)))) {
							arg1_name = "@" + arg1_name;
						}
						std::string arg2_name = opActual(I.getOperand(1))->getName().str();
						if (isa<GlobalObject>(opActual(I.getOperand(1)))) {
							arg2_name = "@" + arg2_name;
						}
						if (arg1_name.compare("")) {
							insert_implies(arg1_name, arg2_name, 0, 1, variables, variables_depth, func_solver);
							insert_implies_only(arg2_name, arg2_name, 0, 1, variables, variables_depth, func_solver);
						}
						else {
							SKIP_DEBUG(errs() << "Skipping ";
							opActual(I.getOperand(0))->dump();)
						}
					}
					else if (BinaryOperator *BO = dyn_cast<BinaryOperator>(Ii)) {
						std::string arg1_name = opActual(BO->getOperand(0))->getName().str();
						if (isa<GlobalObject>(opActual(I.getOperand(0)))) {
							arg1_name = "@" + arg1_name;
						}
						std::string arg2_name = opActual(BO->getOperand(1))->getName().str();
						if (isa<GlobalObject>(opActual(I.getOperand(1)))) {
							arg2_name = "@" + arg2_name;
						}
						std::string var_name = BO->getName().str();
						if (arg1_name.compare(""))
							insert_implies(arg1_name, var_name, 0, 0, variables, variables_depth, func_solver);
						else {
							SKIP_DEBUG(errs() << "Skipping ";
							opActual(BO->getOperand(0))->dump();)
						}
						if (arg2_name.compare(""))
							insert_implies(arg2_name, var_name, 0, 0, variables, variables_depth, func_solver);
						else {
							SKIP_DEBUG(errs() << "Skipping ";
							opActual(BO->getOperand(1))->dump();)
						}
					}
					else if (CmpInst *CI = dyn_cast<CmpInst>(Ii)) {
						std::string arg1_name = opActual(CI->getOperand(0))->getName().str();
						if (isa<GlobalObject>(opActual(I.getOperand(0)))) {
							arg1_name = "@" + arg1_name;
						}
						std::string arg2_name = opActual(CI->getOperand(1))->getName().str();
						if (isa<GlobalObject>(opActual(I.getOperand(1)))) {
							arg2_name = "@" + arg2_name;
						}
						std::string var_name = CI->getName().str();
						if (arg1_name.compare(""))
							insert_implies(arg1_name, var_name, 0, 0, variables, variables_depth, func_solver);
						else {
							SKIP_DEBUG(errs() << "Skipping ";
							opActual(CI->getOperand(0))->dump();)
						}
						if (arg2_name.compare(""))
							insert_implies(arg2_name, var_name, 0, 0, variables, variables_depth, func_solver);
						else {
							SKIP_DEBUG(errs() << "Skipping ";
							opActual(CI->getOperand(1))->dump();)
						}
					}
					else if (ReturnInst *RO = dyn_cast<ReturnInst>(Ii)) {
						if (RO->getNumOperands() == 0)
							continue;
						std::string arg1_name = opActual(RO->getOperand(0))->getName().str();
						if (isa<GlobalObject>(opActual(I.getOperand(0)))) {
							arg1_name = "@" + arg1_name;
						}
						if (arg1_name.compare(""))
							insert_implies(arg1_name, "$result", 0, 0, variables, variables_depth, func_solver);
						else {
							SKIP_DEBUG(errs() << "Skipping ";
							opActual(RO->getOperand(0))->dump();)
						}
					}
					else if (dyn_cast<CallInst>(Ii)!=NULL && !isInSpecialHandleList(*Ii)) {
						
						CallInst *CI = dyn_cast<CallInst>(Ii);
						if (CI->isInlineAsm())
							continue;
						Function *TF = CI->getCalledFunction();
						//errs() << "Doing inference for call statement\n";
						//CI->dump();
						//if (TF == NULL) {
						//	llvm::errs() << "Skipping function call!\n";
						//	continue;
						//}
							
						
						//TF->dump();
						int index = 0;
						std::string type;
						//MDNode *func_md = TF->getMetadata("sgx_type");
						//MDNode *func_ret_node = TF->getMetadata("sgx_return_type");
						MDNode *func_md = CI->getMetadata("sgx_call_type");
						MDNode *func_ret_node = CI->getMetadata("sgx_call_return_type");

						if (func_md == NULL) {
							std::string func_name = TF->getName().str();
							NamedMDNode *md = module->getNamedMetadata("func_sgx_type");
							for (unsigned int i = 0; i < md->getNumOperands(); i++) {
								MDNode *s_md = md->getOperand(i);
								std::string  s_name = dyn_cast<MDString>(s_md->getOperand(0).get())->getString().str();
								if (s_name.compare(func_name) == 0) {
									func_md = dyn_cast<MDNode>(s_md->getOperand(1).get());
									func_ret_node = dyn_cast<MDNode>(s_md->getOperand(2).get());
									break;
								}
							}
						}
						
						for (CallInst::op_iterator Oi = CI->arg_begin(); Oi != CI->arg_end(); Oi++) {

							std::string op_name = opActual(*Oi)->getName();
							if (isa<GlobalObject>(opActual(*Oi))) {
								op_name = "@" + op_name;
							}
							if (op_name.compare("") == 0) {
								SKIP_DEBUG(errs() << "Skipping ";
								opActual(*Oi)->dump();)
									index++;
								continue;
							}
							int op_depth = variables_depth[op_name];
							MDNode* arg_md;
							if (func_md->getNumOperands() <= index) {
								///TODO: NEED TO FIX THIS 
								//errs() << "Overflow in operands, assuming var args with public type !\n";
								//CI->dump();
								//	continue;
								type = "public";
								op_depth = 1;
							}
							else {
								arg_md = dyn_cast<MDNode>(func_md->getOperand(index).get());
								int md_depth = arg_md->getNumOperands();
								op_depth = op_depth < md_depth ? op_depth : md_depth;
								type = dyn_cast<MDString>(arg_md->getOperand(0).get())->getString();
							}

							if (type.compare("public") == 0) {
								z3::expr condition = implies(variables.find(op_name)->second, false_const);
								func_solver.add(condition);
							}
							else {
								z3::expr condition = implies(variables.find(op_name)->second, true_const);
								func_solver.add(condition);
							}
							op_name = op_name + "$p";
							for (int i = 1; i < op_depth; i++) {
								type = dyn_cast<MDString>(arg_md->getOperand(i).get())->getString();
								if (type.compare("public") == 0) {
									z3::expr condition = variables.find(op_name)->second == false_const;
									func_solver.add(condition);
								}
								else {
									z3::expr condition = variables.find(op_name)->second == true_const;
									func_solver.add(condition);
								}
								op_name = op_name + "$p";
							}
							index++;
						}
						
						std::string ret_name = CI->getName();
						if (ret_name.compare("") == 0)
							continue;
						if (isa<GlobalObject>(CI)) {
							ret_name = "@" + ret_name;
						}
						int ret_depth = variables_depth[ret_name];
						int ret_md_depth = func_ret_node->getNumOperands();
						ret_depth = ret_depth < ret_md_depth ? ret_depth : ret_md_depth;
						type = dyn_cast<MDString>(func_ret_node->getOperand(0).get())->getString();
						if (type.compare("public") == 0) {
							z3::expr condition = implies(false_const, variables.find(ret_name)->second);
							func_solver.add(condition);
						}
						else {
							z3::expr condition = implies(true_const, variables.find(ret_name)->second);
							func_solver.add(condition);
						}
						ret_name = ret_name + "$p";
						for (int i = 1; i < ret_depth; i++) {
							type = dyn_cast<MDString>(func_ret_node->getOperand(i).get())->getString();
							if (type.compare("public") == 0) {
								z3::expr condition = variables.find(ret_name)->second == false_const;
								func_solver.add(condition);
							}
							else {
								z3::expr condition = variables.find(ret_name)->second == true_const;
								func_solver.add(condition);
							}
							ret_name = ret_name + "$p";
						}
					}
					else if (CallInst *CI = dyn_cast<CallInst>(Ii)) {

						std::string special_name = dyn_cast<CallInst>(Ii)->getCalledFunction()->getName().str();
					//	errs() << "Special call : " << special_name << "\n";
						if (strncmp(special_name.c_str(), "llvm.memcpy.", 12) == 0) {

						//	errs() << "Inserting memcpy\n";
							std::string arg1_name = opActual(CI->getOperand(0))->getName().str();
							if (isa<GlobalObject>(opActual(I.getOperand(0)))) {
								arg1_name = "@" + arg1_name;
							}
							std::string arg2_name = opActual(CI->getOperand(1))->getName().str();
							if (isa<GlobalObject>(opActual(I.getOperand(1)))) {
								arg2_name = "@" + arg2_name;
							}
							
							if (arg1_name.compare("") && arg2_name.compare("")) {
								insert_implies_only(arg2_name, arg1_name, 0, 0, variables, variables_depth, func_solver);
								insert_implies_only(arg2_name, arg1_name, 1, 1, variables, variables_depth, func_solver);
							}
							else {
								SKIP_DEBUG(errs() << "Skipping ";
								opActual(BO->getOperand(0))->dump();)
							}


						}
					}
					else if (GetElementPtrInst *GI = dyn_cast<GetElementPtrInst>(Ii)) {
						//GI->dump();
						//Type *ty = opActual(GI->getOperand(0))->getType();
						Type *ty = GI->getOperand(0)->getType();

						

						std::string result = GI->getName().str();
						std::string param = opActual(GI->getOperand(0))->getName();
						if (dyn_cast<ConstantPointerNull>(opActual(GI->getOperand(0)))) {
							continue;
						}
						if (isa<GlobalObject>(opActual(I.getOperand(0)))) {
							param = "@" + param;
						}
						
						if (ty->getPointerElementType()->isStructTy()) {	
							if (dyn_cast<StructType>(ty->getPointerElementType())->isLiteral()){
								if (dyn_cast<ConstantExpr>(GI->getOperand(0)) && dyn_cast<ConstantExpr>(GI->getOperand(0))->isCast()) {
									ty = dyn_cast<ConstantExpr>(GI->getOperand(0))->getType();
								}
								if(dyn_cast<BitCastInst>(GI->getOperand(0))){
									ty = dyn_cast<BitCastInst>(GI->getOperand(0))->getOperand(0)->getType();
								}
							}
						}

						if (GI->getNumIndices() == 2 && ty->getPointerElementType()->isStructTy()) {
							
							//ty->getPointerElementType()->dump();
							if (opActual(GI->getOperand(1))->getName().str().compare("") != 0) {
								
								std::string arg1_name = opActual(GI->getOperand(1))->getName().str();
								if (isa<GlobalObject>(opActual(GI->getOperand(1)))) {
									arg1_name = "@" + arg1_name;
								}
								std::string var_name = GI->getName().str();
								insert_implies(arg1_name, var_name, 0, 0, variables, variables_depth, func_solver);
							}
							else {
								SKIP_DEBUG(errs() << "Skipping ";
								opActual(GI->getOperand(1))->dump();)
							}
							std::string struct_name = ty->getPointerElementType()->getStructName().str();
							
							//z3::expr condition = variables.find(result)->second == variables.find(param)->second;
							//func_solver.add(condition);
							insert_implies_only(param, result, 0, 0, variables, variables_depth, func_solver);
							
							z3::expr condition2 = variables.find(result + "$p")->second == variables.find(param + "$p")->second;
							func_solver.add(condition2);
							int res_depth = variables_depth[result];
							result = result + "$p";
							param = param + "$p";



							if (res_depth > 2 && strncmp(struct_name.c_str(), "union.", strlen("union."))    ) {
								Module* module = GI->getModule();
								NamedMDNode *md = module->getNamedMetadata("struct_sgx_type");
								MDNode *struct_md;
								for (unsigned int i = 0; i < md->getNumOperands(); i++) {
									MDNode *s_md = md->getOperand(i);
									std::string  s_name = dyn_cast<MDString>(s_md->getOperand(0).get())->getString().str();
									if (s_name.compare(struct_name) == 0) {
										struct_md = dyn_cast<MDNode>(s_md->getOperand(1).get());
										break;
									}
								}

								int f_id = dyn_cast<ConstantInt>(GI->idx_end()-1)->getZExtValue();
								MDNode *field_md = dyn_cast<MDNode>(struct_md->getOperand(f_id).get());	
								
								for (int i = 2; i < res_depth; i++) {
									bool sgx_type;
									std::string sgx_string = dyn_cast<MDString>(field_md->getOperand(i-2).get())->getString().str();
									sgx_type = sgx_string.compare("private") == 0;
									result = result + "$p";
									if (sgx_type) {
										z3::expr condition = variables.find(result)->second == true_const;
										func_solver.add(condition);
									}
									else {
										z3::expr condition = variables.find(result)->second == false_const;
										func_solver.add(condition);
									}
								}
							}	
						}
						/*else if (GI->getNumIndices() == 1) {
							z3::expr condition = variables.find(result)->second == variables.find(param)->second;
							insert_implies(param, result, 0, 0, variables, variables_depth, func_solver);
							if (opActual(GI->getOperand(1))->getName().str().compare("") != 0) {
								
								std::string arg1_name = opActual(GI->getOperand(1))->getName().str();
								if (isa<GlobalObject>(opActual(GI->getOperand(1)))) {
									arg1_name = "@" + arg1_name;
								}
								std::string var_name = GI->getName().str();
								insert_implies(arg1_name, var_name, 0, 0, variables, variables_depth, func_solver);
							}
							else {
								errs() << "Skipping ";
								opActual(GI->getOperand(1))->dump();
							}
						}*/
						else {
							z3::expr condition = variables.find(result)->second == variables.find(param)->second;
							insert_implies(param, result, 0, 0, variables, variables_depth, func_solver);
							for (unsigned int i = 0; i < GI->getNumIndices(); i++) {
								if (opActual(GI->getOperand(i+1))->getName().str().compare("") != 0) {
									std::string arg1_name = opActual(GI->getOperand(i+1))->getName().str();
									if (isa<GlobalObject>(opActual(GI->getOperand(i+1)))) {
										arg1_name = "@" + arg1_name;
									}
									std::string var_name = GI->getName().str();
									insert_implies(arg1_name, var_name, 0, 0, variables, variables_depth, func_solver);
								}
								else {
									SKIP_DEBUG(errs() << "Skipping ";
									opActual(GI->getOperand(1))->dump();)
								}
							}
						}
					}
					else if (dyn_cast<AllocaInst>(Ii) != NULL) {
					}
					else if (dyn_cast<UnaryInstruction>(Ii)!=NULL) {
						if (dyn_cast<BitCastInst>(Ii) != NULL) {
							std::string var_name = Ii->getName().str();
							MDNode *md_node = Ii->getMetadata("sgx_cast_type");
							if (!md_node) {
								//llvm_unreachable("Bitcast with no md found!\n");
							}
							else {
								int total = variables_depth[var_name];
								for (int i = 0; i < total; i++) {
									std::string sgx_type = dyn_cast<MDString>(md_node->getOperand(i).get())->getString().str();
									if (sgx_type.compare("private") == 0) {
										z3::expr condition = variables.find(var_name)->second == true_const;
										func_solver.add(condition);
									}
									var_name = var_name + "$p";
								}
							}
							
						}
						UnaryInstruction *UI = dyn_cast<UnaryInstruction>(Ii);
						std::string arg1_name = opActual(UI->getOperand(0))->getName().str();
						if (isa<GlobalObject>(opActual(I.getOperand(0)))) {
							arg1_name = "@" + arg1_name;
						}
						std::string var_name = UI->getName().str();
						if (arg1_name.compare(""))
							insert_implies(arg1_name, var_name, 0, 0, variables, variables_depth, func_solver);
						else {
							SKIP_DEBUG(errs() << "Skipping ";
							opActual(UI->getOperand(0))->dump();)
						}
					}
					else if (PHINode* PI = dyn_cast<PHINode>(Ii)) {
						
						std::string var_name = PI->getName().str();
						for (unsigned int i = 0; i < PI->getNumIncomingValues(); i++) {
							Value *incoming = opActual(PI->getIncomingValue(i));
							std::string incoming_name = incoming->getName().str();
							if (isa<GlobalObject>(incoming)) {
								incoming_name = "@" + incoming_name;
							}
							if(incoming_name.compare(""))
								insert_implies(incoming_name, var_name, 0, 0, variables, variables_depth, func_solver);
							else {
								SKIP_DEBUG(errs() << "Skipping ";
								incoming->dump();)
							}
						}
					}
					else if (SelectInst *SI = dyn_cast<SelectInst>(Ii)) {
						std::string var_name = SI->getName().str();
						Value *true_value = opActual(SI->getTrueValue());
						Value *false_value = opActual(SI->getFalseValue());
						std::string true_value_name = true_value->getName().str();
						std::string false_value_name = false_value->getName().str();
						if (isa<GlobalObject>(true_value)) {
							true_value_name = "@" + true_value_name;
						}
						if (isa<GlobalObject>(false_value)) {
							false_value_name = "@" + false_value_name;
						}
						if (true_value_name.compare("")) {
							insert_implies(true_value_name, var_name, 0, 0, variables, variables_depth, func_solver);
						}
						else {
							SKIP_DEBUG(errs() << "Skipping ";
							true_value->dump();)
						}
						if (false_value_name.compare("")) {
							insert_implies(false_value_name, var_name, 0, 0, variables, variables_depth, func_solver);
						}
						else {
							SKIP_DEBUG(errs() << "Skipping ";
							false_value->dump();)
						}
					}
					else if (AtomicRMWInst *AI = dyn_cast<AtomicRMWInst>(Ii)) {
						std::string var_name = AI->getName().str();
						std::string ptr_name = opActual(AI->getPointerOperand())->getName().str();
						std::string val_name = opActual(AI->getValOperand())->getName().str();
						
						if(isa<GlobalObject>(opActual(AI->getPointerOperand()))) {
							ptr_name = "@" + ptr_name;
						}	
						if(isa<GlobalObject>(opActual(AI->getValOperand()))) {
							val_name = "@" + val_name;
						}	
						if (ptr_name.compare("") && val_name.compare("")) {
							insert_implies(ptr_name, var_name, 1, 0, variables, variables_depth, func_solver);
							insert_implies_only(ptr_name, var_name, 0, 0, variables, variables_depth, func_solver);
							insert_implies_only(ptr_name, ptr_name, 0, 1, variables, variables_depth, func_solver);
							insert_implies(val_name, ptr_name, 0, 1, variables, variables_depth, func_solver);
						}else {
							SKIP_DEBUG(errs() << "Skipping ";
							opActual(I.getPointerOperand())->dump();)	
						}
					}
					else if (AtomicCmpXchgInst *AI = dyn_cast<AtomicCmpXchgInst>(Ii)) {
						std::string var_name = AI->getName().str();
						std::string ptr_name = opActual(AI->getPointerOperand())->getName().str();
						std::string val_name = opActual(AI->getNewValOperand())->getName().str();
						std::string cmp_name = opActual(AI->getCompareOperand())->getName().str();

						if(isa<GlobalObject>(opActual(AI->getPointerOperand()))) {
							ptr_name = "@" + ptr_name;
						}	
						if(isa<GlobalObject>(opActual(AI->getNewValOperand()))) {
							val_name = "@" + val_name;
						}	
						if(isa<GlobalObject>(opActual(AI->getCompareOperand()))) {
							cmp_name = "@" + cmp_name;
						}	
						if (ptr_name.compare("") && val_name.compare("") && cmp_name.compare("")) {
							insert_implies(ptr_name, var_name, 1, 0, variables, variables_depth, func_solver);

							insert_implies_only(ptr_name, var_name, 0, 0, variables, variables_depth, func_solver);
							insert_implies_only(ptr_name, ptr_name, 0, 1, variables, variables_depth, func_solver);

							insert_implies(val_name, ptr_name, 0, 1, variables, variables_depth, func_solver);
							insert_implies(cmp_name, ptr_name, 0, 1, variables, variables_depth, func_solver);
						}else {
							SKIP_DEBUG(errs() << "Skipping ";
							opActual(I.getPointerOperand())->dump();)	
						}
					}
					else {
						if (I.getName().compare("")) {
							errs() << "No inference for :";
							Ii->dump();
						}
						
					}
				}
			}
			
			bool solved = func_solver.check();
			if (solved == false) {
				errs() << "No solution for annotations inference in function "<< F.getName().str() << "\n"; 
				llvm_unreachable(("No solution for annotations inference in function "+F.getName().str()+". Check for invalid assignments!\n").c_str());
				return false;
			}
			(void)solved;
			z3::model func_model = func_solver.get_model();
			

			/*
			for (auto Vi = variables.begin(); Vi != variables.end(); Vi++ ) {
				std::ostringstream ss;
				ss << func_model.eval(Vi->second);
				std::string type = ss.str().compare("true") == 0 ? "private" : "public";
				//errs() << Vi->first << ":" << type <<"\n";
			}
			*/

			for (Function::iterator BBi = F.begin(); BBi != F.end(); BBi++) {
				BasicBlock &BB = *BBi;
				for (BasicBlock::iterator Ii = BB.begin(); Ii != BB.end(); Ii++) {
					Instruction &I = *Ii;
					
					if (I.getName().compare("") == 0)
						continue;
					std::string var_name = I.getName().str();
					int depth = variables_depth[var_name];
					std::vector<Metadata*> md_array;
					for (int i = 0; i < depth; i++) {
						std::ostringstream ss;
						
						func_solver.push();
						func_solver.add(variables.find(var_name)->second == false_const);
						
						bool canPublic = func_solver.check();
						//errs() << var_name << " = " << canPublic<< "\n";
						std::string type = canPublic ? "public" : "private";
						func_solver.pop();
						

						//ss << func_model.eval(variables.find(var_name)->second);
						//std::string type = ss.str().compare("true") == 0 ? "private" : "public";
						
						md_array.push_back(MDString::get(F.getContext(), type));
						var_name = var_name + "$p";
					}
					MDNode *md_node = MDNode::get(F.getContext(), ArrayRef<Metadata*>(md_array));
					I.setMetadata("sgx_type", md_node);
				}
			}
			//errs() << "Completed inference\n";
			static int printed = false;
			if (printed)
				return false;
			NamedMDNode *func_md = module->getNamedMetadata("func_sgx_type");
			if (func_md == NULL)
				return false;
			printed = true;
			if (lfFileName.compare("") == 0)
				return false;
			std::fstream lf_file;
			lf_file.open(lfFileName.c_str(), std::ios::out);
			for (int i = 0; i < func_md->getNumOperands(); i++) {
				
				MDNode *md_entry = func_md->getOperand(i);
				std::string fname = dyn_cast<MDString>(md_entry->getOperand(0))->getString().str();
				if (module->getNamedValue(fname) == NULL)
					continue;
				MDNode* args = dyn_cast<MDNode>(md_entry->getOperand(1));
				MDNode* ret_md = dyn_cast<MDNode>(md_entry->getOperand(2));
				lf_file << dyn_cast<MDString>(ret_md->getOperand(0))->getString().str() << "\t";
				lf_file << fname << "\t";
				int num_args = ((args->getNumOperands()) < 6) ? args->getNumOperands() : 6;
					
				Function *func = dyn_cast<Function>(module->getNamedValue(fname));
				if (func->isVarArg())
					num_args = 6;
				for (int j = 0; j < num_args; j++) {
					if (j>=args->getNumOperands())
						lf_file << "public";
					else {
						MDNode *arg_md = dyn_cast<MDNode>(args->getOperand(j));
						lf_file << dyn_cast<MDString>(arg_md->getOperand(0))->getString().str();
					}
						
					if (j != num_args-1)
						lf_file << ", ";
				}
				lf_file << "\t" << (func->isVarArg() ? 16 : args->getNumOperands()) << "\n";
			}
			lf_file.close();
			return false;
			
		}
		virtual void getAnalysisUsage(AnalysisUsage& Info) {
			Info.setPreservesAll();
		}
	};
}

char AnnotationsInference::ID = 0;

INITIALIZE_PASS(AnnotationsInference, "annotations-inference", "Infer annotations for all instructions in the functions", false, false);

FunctionPass *llvm::createAnnotationsInferencePass() {
	return new AnnotationsInference();
}
