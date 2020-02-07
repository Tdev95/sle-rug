module Check
import IO;
import AST;
import Resolve;
import Message; // see standard library
import Set;

data Type
  = tint()
  | tbool()
  | tstr()
  | tunknown()
  ;

// the type environment consisting of defined questions in the form 
alias TEnv = rel[loc def, str name, str label, Type \type];

// To avoid recursively traversing the form, use the `visit` construct
// or deep match (e.g., `for (/question(...) := f) {...}` ) 
TEnv collect(AForm f) {
  return {< q.src, id.name, label, AType2Type(t)> | /q:question(str label, AId id, AType t, _) := f}; 
}

Type AType2Type(AType at){
	switch(at){
		case \type("boolean"): return tbool();
		case \type("integer"): return tint();
		default: {return tunknown();}
	}
}

set[Message] check(AForm f, TEnv tenv, UseDef useDef){
  set[Message] msgs = {};
  for(/q:question(str _, AId _, AType _, list[AExpr] _) := f){
  	msgs += check(q, tenv, useDef);
  }
  return msgs; 
}

// - produce an error if there are declared questions with the same name but different types.
// - duplicate labels should trigger a warning 
// - the declared type computed questions should match the type of the expression.

set[Message] check(AQuestion q, TEnv tenv, UseDef useDef) {
	set[Message] msgs = {};
	// obtain label
	str label;
	Type tp;
	list[AExpr] aexpr = [];
	for(/question(str l, _, AType t, list[AExpr] axprs) := q){
		label = l;
		tp = AType2Type(t);
		aexpr = axprs;
	}
	// same label twice
	list[str] labels = [label | /<_, _, label, _> := tenv];
	
	if(labels != [label]){
		msgs += warning("<q.src>" + "Duplicate label");
	}
	
	// same label, different types
	set[Type] types = {t | /<_, _, label, Type t> := tenv};
	if(types != {AType2Type(q.\type)}){
		msgs += error("<q.src>" + "Same label, different type");
	}
	
	// type of expression != type of question
	//checking the expressions operand compatibility
	if(aexpr != []){
		for(exp <- aexpr){
			msgs += check(exp, tenv, useDef);	
		}
		Type etp = typeOf(aexpr[0], tenv, useDef);
		if(etp != tunknown() && etp != tp){
			msgs += error("<q.src>" + "Type of expression does not match type of question");
		}
	}
	
	return msgs;
}

// Check operand compatibility with operators.
// E.g. for an addition node add(lhs, rhs), 
//   the requirement is that typeOf(lhs) == typeOf(rhs) == tint()
set[Message] check(AExpr e, TEnv tenv, UseDef useDef) {
  set[Message] msgs = {};
  
  switch (e) {
  	case not(AExpr ex):{
  		if(typeOf(e, tenv,useDef) != tbool()){
  			msgs += error("<e.src>" + "Operand Uncompatible with Operators");
  		}
  		msgs += check(ex, tenv, useDef);
  	}
    	
    case divide(AExpr expr1, AExpr expr2): {
  		if(typeOf(expr1, tenv,useDef) != typeOf(expr2, tenv,useDef) || typeOf(expr1, tenv,useDef) != tint()){
  			msgs += error("<e.src>" + "Operand Uncompatible with Operators");
  		}
  		msgs += check(expr1, tenv, useDef);
  		msgs += check(expr2, tenv, useDef);
    }
    case multiply(AExpr expr1, AExpr expr2): {
  		if(typeOf(expr1, tenv,useDef) != typeOf(expr2, tenv,useDef) || typeOf(expr1, tenv,useDef) != tint()){
  			msgs += error("<e.src>" + "Operand Uncompatible with Operators");
  		}
  		msgs += check(expr1, tenv, useDef);
  		msgs += check(expr2, tenv, useDef);
    }
    case add(AExpr expr1, AExpr expr2): {
  		if(typeOf(expr1, tenv,useDef) != typeOf(expr2, tenv,useDef) || typeOf(expr1, tenv,useDef) != tint()){
  			msgs += error("<e.src>" + "Operand Uncompatible with Operators");
  		}
  		msgs += check(expr1, tenv, useDef);
  		msgs += check(expr2, tenv, useDef);
    }
    case subtract(AExpr expr1, AExpr expr2): {
  		if(typeOf(expr1, tenv,useDef) != typeOf(expr2, tenv,useDef) || typeOf(expr1, tenv,useDef) != tint()){
  			msgs += error("<e.src>" + "Operand Uncompatible with Operators");
  		}
  		msgs += check(expr1, tenv, useDef);
  		msgs += check(expr2, tenv, useDef);
    }
    case less(AExpr expr1, AExpr expr2): {
  		if(typeOf(expr1, tenv,useDef) != typeOf(expr2, tenv,useDef) || typeOf(expr1, tenv,useDef) != tbool()){
  			msgs += error("<e.src>" + "Operand Uncompatible with Operators");
  		}
  		msgs += check(expr1, tenv, useDef);
  		msgs += check(expr2, tenv, useDef);
    }
    case gtr(AExpr expr1, AExpr expr2): {
  		if(typeOf(expr1, tenv,useDef) != typeOf(expr2, tenv,useDef) || typeOf(expr1, tenv,useDef) != tbool()){
  			msgs += error("<e.src>" + "Operand Uncompatible with Operators");
  		}
  		msgs += check(expr1, tenv, useDef);
  		msgs += check(expr2, tenv, useDef);
    }
    case leq(AExpr expr1, AExpr expr2): {
  		if(typeOf(expr1, tenv,useDef) != typeOf(expr2, tenv,useDef) || typeOf(expr1, tenv,useDef) != tbool()){
  			msgs += error("<e.src>" + "Operand Uncompatible with Operators");
  		}
  		msgs += check(expr1, tenv, useDef);
  		msgs += check(expr2, tenv, useDef);
    }
    case geq(AExpr expr1, AExpr expr2): {
  		if(typeOf(expr1, tenv,useDef) != typeOf(expr2, tenv,useDef) || typeOf(expr1, tenv,useDef) != tbool()){
  			msgs += error("<e.src>" + "Operand Uncompatible with Operators");
  		}
  		msgs += check(expr1, tenv, useDef);
  		msgs += check(expr2, tenv, useDef);
    }
    case eq(AExpr expr1, AExpr expr2): {
  		if(typeOf(expr1, tenv,useDef) != typeOf(expr2, tenv,useDef) || typeOf(expr1, tenv,useDef) != tbool()){
  			msgs += error("<e.src>" + "Operand Uncompatible with Operators");
  		}
  		msgs += check(expr1, tenv, useDef);
  		msgs += check(expr2, tenv, useDef);
    }
    case neq(AExpr expr1, AExpr expr2): {
  		if(typeOf(expr1, tenv,useDef) != typeOf(expr2, tenv,useDef) || typeOf(expr1, tenv,useDef) != tbool()){
  			msgs += error("<e.src>" + "Operand Uncompatible with Operators");
  		}
  		msgs += check(expr1, tenv, useDef);
  		msgs += check(expr2, tenv, useDef);
    }
    case and(AExpr expr1, AExpr expr2): {
  		if(typeOf(expr1, tenv,useDef) != typeOf(expr2, tenv,useDef) || typeOf(expr1, tenv,useDef) != tbool()){
  			msgs += error("<e.src>" + "Operand Uncompatible with Operators");
  		}
  		msgs += check(expr1, tenv, useDef);
  		msgs += check(expr2, tenv, useDef);
    }
    case or(AExpr expr1, AExpr expr2): {
  		if(typeOf(expr1, tenv,useDef) != typeOf(expr2, tenv,useDef) || typeOf(expr1, tenv,useDef) != tbool()){
  			msgs += error("<e.src>" + "Operand Uncompatible with Operators");
  		}
  		msgs += check(expr1, tenv, useDef);
  		msgs += check(expr2, tenv, useDef);
    }
    case ref(str x, src = loc u):
      msgs += { error("Undeclared question", u) | useDef[u] == {} };
  } 
  return msgs; 
}

Type typeOf(AExpr e, TEnv tenv, UseDef useDef) {
  switch (e) {
    case brackets(AExpr ex):
      return typeOf(ex, tenv, useDef);
    case not(AExpr ex): {
      if(typeOf(ex, tenv, useDef) == tbool()){
      	return tbool();
      }
      else{
      	return tunknown();
      }
    }
    case divide(AExpr expr1, AExpr expr2): {
      if(typeOf(expr1, tenv, useDef) == tint() && typeOf(expr2, tenv, useDef) == tint()){
      	return tint();
      }
      else{
      	return tunknown();
      }
    }
    case multiply(AExpr expr1, AExpr expr2): {
      if(typeOf(expr1, tenv, useDef) == tint() && typeOf(expr2, tenv, useDef) == tint()){
      	return tint();
      }
      else{
      	return tunknown();
      }
    }
    case add(AExpr expr1, AExpr expr2): {
      if(typeOf(expr1, tenv, useDef) == tint() && typeOf(expr2, tenv, useDef) == tint()){
      	return tint();
      }
      else{
      	return tunknown();
      }
    }
    case subtract(AExpr expr1, AExpr expr2): {
      if(typeOf(expr1, tenv, useDef) == tint() && typeOf(expr2, tenv, useDef) == tint()){
      	return tint();
      }
      else{
      	return tunknown();
      }
    }
    case less(AExpr expr1, AExpr expr2): {
      if(typeOf(expr1, tenv, useDef) == tint() && typeOf(expr2, tenv, useDef) == tint()){
      	return tbool();
      }
      else{
      	return tunknown();
      }
    }
    case gtr(AExpr expr1, AExpr expr2): {
      if(typeOf(expr1, tenv, useDef) == tint() && typeOf(expr2, tenv, useDef) == tint()){
      	return tbool();
      }
      else{
      	return tunknown();
      }
    }
    case leq(AExpr expr1, AExpr expr2): {
      if(typeOf(expr1, tenv, useDef) == tint() && typeOf(expr2, tenv, useDef) == tint()){
      	return tbool();
      }
      else{
      	return tunknown();
      }
    }
    case geq(AExpr expr1, AExpr expr2): {
      if(typeOf(expr1, tenv, useDef) == tint() && typeOf(expr2, tenv, useDef) == tint()){
      	return tbool();
      }
      else{
      	return tunknown();
      }
    }
    case eq(AExpr expr1, AExpr expr2): {
      if(typeOf(expr1, tenv, useDef) == tint() && typeOf(expr2, tenv, useDef) == tint()){
      	return tbool();
      }
      else{
      	return tunknown();
      }
    }
    case neq(AExpr expr1, AExpr expr2): {
      if(typeOf(expr1, tenv, useDef) == tint() && typeOf(expr2, tenv, useDef) == tint()){
      	return tbool();
      }
      else{
      	return tunknown();
      }
    }
    case and(AExpr expr1, AExpr expr2): {
      if(typeOf(expr1, tenv, useDef) == tbool() && typeOf(expr2, tenv, useDef) == tbool()){
      	return tbool();
      }
      else{
      	return tunknown();
      }
    }
    case or(AExpr expr1, AExpr expr2): {
      if(typeOf(expr1, tenv, useDef) == tbool() && typeOf(expr2, tenv, useDef) == tbool()){
      	return tbool();
      }
      else{
      	return tunknown();
      }
    }
    case ref(str x, src = loc u):  
      if (<u, loc d> <- useDef, <d, x, _, Type t> <- tenv) {
        return t;
      }
    case integer(int n):
      return tint();
    case boolean(str \bool):
      return tbool();

  }
  return tunknown(); 
}

/* 
 * Pattern-based dispatch style:
 * 
 * Type typeOf(ref(str x, src = loc u), TEnv tenv, UseDef useDef) = t
 *   when <u, loc d> <- useDef, <d, x, _, Type t> <- tenv
 *
 * ... etc.
 * 
 * default Type typeOf(AExpr _, TEnv _, UseDef _) = tunknown();
 *
 */
 
 

