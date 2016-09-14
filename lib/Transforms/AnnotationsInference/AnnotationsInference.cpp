#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Transforms/AnnotationsInference.h"
#include "llvm/Support/raw_ostream.h"
#include "c++/z3++.h"
#include "llvm/IR/Instructions.h"
#include <fstream>
#include <map>
#include "z3.h"
#include "llvm/Transforms/Scalar.h"
using namespace llvm;

namespace {
	struct AnnotationsInference : public FunctionPass {
		static char ID;
		static std::map<std::string, std::vector<std::string>> function_signatures;

		AnnotationsInference() : FunctionPass(ID) {
			initializeAnnotationsInferencePass(*PassRegistry::getPassRegistry());
			std::fstream signature_file;
			signature_file.open("signatures.md", std::ios::in);
			std::string line;
			std::string present_function;
			while (std::getline(signature_file, line)) {
				if (line[0] != '\t') {
					present_function = line;
				}
				else {
					line.erase(0, 1);
					function_signatures[present_function].push_back(line);
				}
			}
			signature_file.close();

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
			z3::expr condition = implies(variables.find(LHS_name)->second, variables.find(RHS_name)->second);
			func_solver.add(condition);
			errs() << "Inserted condition : " << LHS_name << " => " << RHS_name << "\n";
			LHS_depth++;
			RHS_depth++;
			while (LHS_depth < variables_depth[LHS] && RHS_depth < variables_depth[RHS]) {
				LHS_name = LHS_name + "$p";
				RHS_name = RHS_name + "$p";
				z3::expr condition = (variables.find(LHS_name)->second == variables.find(RHS_name)->second);
				func_solver.add(condition);
				errs() << "Inserted condition : " << LHS_name << " == " << RHS_name << "\n";
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
			errs() << "Inserted condition : " << LHS_name << " => " << RHS_name << "\n";
			return;
		}
		bool runOnFunction(Function &F) override {
			errs() << "Inferring annotations for : " << F.getName() << "\n";
			if (function_signatures.find(F.getName().str()) == function_signatures.end()) {
				errs() << "Signatures for " << F.getName() << " not found. Run signature dump again\n";
				return false;
			}
			z3::context func_context;
			z3::solver func_solver(func_context);
			

			z3::expr true_const = func_context.bool_val(true);
			z3::expr false_const = func_context.bool_val(false);

			std::map<std::string, z3::expr> variables;
			std::map<std::string, int> variables_depth;

			Type *ty = F.getReturnType();
			std::string var_name = "$result";
			int depth = 1;
			std::istringstream annotation(function_signatures[F.getName().str()][0]);
			while (ty->isPointerTy()) {
				errs() << "Creating var : " << var_name << "\n";
				variables.insert(std::pair<std::string, z3::expr>(var_name, func_context.bool_const(var_name.c_str())));
				ty = ty->getPointerElementType();
				std::string type;
				if (!(annotation >> type))
					assert(false && "Inadequate number of constraints on arguments");
				errs() << "Type = " << type << "\n";
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
			errs() << "Creating var : " << var_name << "\n";
			variables.insert(std::pair<std::string, z3::expr>(var_name, func_context.bool_const(var_name.c_str())));
			std::string type;
			if (!(annotation >> type))
				assert(false && "Inadequate number of constraints on arguments");
			errs() << "Type = " << type << "\n";
			if (type.compare("public") == 0) {
				z3::expr condition = variables.find(var_name)->second == false_const;
				func_solver.add(condition);
			}
			else {
				z3::expr condition = variables.find(var_name)->second == true_const;
				func_solver.add(condition);
			}
			variables_depth["$result"] = depth;



			int arg_order = 1;
			for (Function::arg_iterator Ai = F.arg_begin(); Ai != F.arg_end(); Ai++) {
				std::istringstream annotation(function_signatures[F.getName().str()][arg_order]);
				arg_order++;
				Argument &A = *Ai;
				std::string arg_name = A.getName().str();
				Type *ty = A.getType();
				int depth = 1;
				while (ty->isPointerTy()) {
					errs() << "Creating var : " << arg_name << "\n";
					variables.insert(std::pair<std::string, z3::expr>(arg_name, func_context.bool_const(arg_name.c_str())));
					ty = ty->getPointerElementType();
					std::string type;
					if (!(annotation >> type))
						assert(false && "Inadequate number of constraints on arguments");
					errs() << "Type = " << type << "\n";
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
				errs() << "Creating var : " << arg_name << "\n";
				variables.insert(std::pair<std::string, z3::expr>(arg_name, func_context.bool_const(arg_name.c_str())));
				std::string type;
				if (!(annotation >> type))
					assert(false && "Inadequate number of constraints on arguments");
				errs() << "Type = " << type << "\n";
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
							errs() << "Creating var : " << var_name << "\n";
							variables.insert(std::pair<std::string, z3::expr>(var_name, func_context.bool_const(var_name.c_str())));
							var_name = var_name + "$p";
							ty = ty->getPointerElementType();
							depth++;
						}
						errs() << "Creating var : " << var_name << "\n";
						variables.insert(std::pair<std::string, z3::expr>(var_name, func_context.bool_const(var_name.c_str())));
						variables_depth[I.getName().str()] = depth;
					}
				}
			}
			for (Function::iterator BBi = F.begin(); BBi != F.end(); BBi++) {
				BasicBlock &BB = *BBi;
				for (BasicBlock::iterator Ii = BB.begin(); Ii != BB.end(); Ii++) {
					Instruction &I = *Ii;
					if (I.getOpcode() == Instruction::Load) {
						std::string var_name = I.getName().str();
						std::string arg_name = I.getOperand(0)->getName().str();
						insert_implies(arg_name, var_name, 1, 0, variables, variables_depth, func_solver);
						insert_implies_only(arg_name, var_name, 0, 0, variables, variables_depth, func_solver);
					}
					else if (I.getOpcode() == Instruction::Store) {
						std::string arg1_name = I.getOperand(0)->getName().str();
						std::string arg2_name = I.getOperand(1)->getName().str();
						if (arg1_name.compare(""))
							insert_implies(arg1_name, arg2_name, 0, 1, variables, variables_depth, func_solver);
					}
					else if (BinaryOperator *BO = dyn_cast<BinaryOperator>(Ii)) {
						std::string arg1_name = BO->getOperand(0)->getName().str();
						std::string arg2_name = BO->getOperand(1)->getName().str();
						std::string var_name = BO->getName().str();
						if (arg1_name.compare(""))
							insert_implies(arg1_name, var_name, 0, 0, variables, variables_depth, func_solver);
						if (arg2_name.compare(""))
							insert_implies(arg2_name, var_name, 0, 0, variables, variables_depth, func_solver);
					}
					else if (ReturnInst *RO = dyn_cast<ReturnInst>(Ii)) {
						if (RO->getNumOperands() == 0)
							continue;
						std::string arg1_name = RO->getOperand(0)->getName().str();
						if (arg1_name.compare(""))
							insert_implies(arg1_name, "$result", 0, 0, variables, variables_depth, func_solver);
					}
				}
			}
			
			bool solved = func_solver.check();
			
			z3::model func_model = func_solver.get_model();
			
			for (auto Vi = variables.begin(); Vi != variables.end(); Vi++ ) {
				std::ostringstream ss;
				ss << func_model.eval(Vi->second);
				std::string type = ss.str().compare("true") == 0 ? "private" : "public";
				errs() << Vi->first << ":" << type <<"\n";
			}
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
						ss << func_model.eval(variables.find(var_name)->second);
						std::string type = ss.str().compare("true") == 0 ? "private" : "public";
						md_array.push_back(MDString::get(F.getContext(), type));
						var_name = var_name + "$p";
					}
					MDNode *md_node = MDNode::get(F.getContext(), ArrayRef<Metadata*>(md_array));
					I.setMetadata("sgx_type", md_node);
				}
			}


			return false;
		}
		virtual void getAnalysisUsage(AnalysisUsage&Info) {
			Info.setPreservesAll();
		}
	};
}

char AnnotationsInference::ID = 0;
std::map<std::string, std::vector<std::string>> AnnotationsInference::function_signatures;

INITIALIZE_PASS(AnnotationsInference, "annotations-inference", "Infer annotations for all instructions in the functions", false, false);

FunctionPass *llvm::createAnnotationsInferencePass() {
	return new AnnotationsInference();
}
