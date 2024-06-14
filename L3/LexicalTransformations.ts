import { ClassExp, ProcExp, Exp, Program ,makeLetExp,isBinding, DefineExp, isLitExp,makeDefineExp} from "./L3-ast";
import { Binding, makeProcExp, makeVarDecl, CExp, makeIfExp,makeBoolExp, makeAppExp} from "./L3-ast";
import{ makePrimOp , makeVarRef, makeLitExp,IfExp,isClassExp,isExp,makeProgram,BoolExp,makeBinding} from "./L3-ast";
import { Result, makeOk, makeFailure, bind, mapResult, mapv } from "../shared/result";
import { map, zipWith ,reduce,reverse} from "ramda";
import { isAtomicExp, isProcExp, isIfExp, isAppExp, isPrimOp, isLetExp, isDefineExp, isProgram } from "./L3-ast";


export const method2test = (method: Binding): CExp =>{
    return makeAppExp(makePrimOp("eq?"),[makeVarRef("msg"),makeLitExp("'" + method.var.var)]);
}

export const method2then = (method: Binding): CExp =>{
    return makeAppExp(method.val,[]);
}

/*
Purpose: Transform ClassExp to ProcExp
Signature: class2proc(classExp)
Type: ClassExp => ProcExp
*/
export const class2proc = (exp: ClassExp): ProcExp =>{
   
    const fields = exp.fields;
    const methods = exp.methods;
    const recursiveIfs = reduce((acc,meth)=>makeIfExp(method2test(meth),method2then(meth),acc) as CExp,makeBoolExp(false) as CExp,reverse(methods));    
    return makeProcExp(fields, [makeProcExp([makeVarDecl("msg")],[recursiveIfs])]);
}


export const includeDifine = (exp: Exp): Exp => 
    isDefineExp(exp)? makeDefineExp(exp.var,expToNoClassExp(exp.val)):
    expToNoClassExp(exp);

export const expToNoClassExp = (exp: CExp): CExp => 
    isAtomicExp(exp) || isLitExp(exp) || isPrimOp(exp) ? exp:
    isClassExp(exp)? class2proc(exp):
    isAppExp(exp) ? makeAppExp(expToNoClassExp(exp.rator), map(expToNoClassExp,exp.rands)):
    isIfExp(exp) ? makeIfExp(expToNoClassExp(exp.test),expToNoClassExp(exp.then),expToNoClassExp(exp.alt)):
    isProcExp(exp) ?  makeProcExp(exp.args,map(expToNoClassExp,exp.body)):
    makeLetExp(map(b => makeBinding(b.var.var,expToNoClassExp(b.val)),exp.bindings),map(expToNoClassExp,exp.body));
    // todo check if there are more options
    
/*
Purpose: Transform all class forms in the given AST to procs
Signature: lexTransform(AST)
Type: [Exp | Program] => Result<Exp | Program>
*/
export const lexTransform = (exp: Exp | Program): Result<Exp | Program> =>
    isExp(exp)? makeOk(includeDifine(exp)) :
    makeOk(makeProgram(map(includeDifine,exp.exps)));
