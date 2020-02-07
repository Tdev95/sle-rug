module Compile

import AST;
import Resolve;
import IO;
import lang::html5::DOM; // see standard library
import math;
import String;

/*
 * Implement a compiler for QL to HTML and Javascript
 *
 * - assume the form is type- and name-correct
 * - separate the compiler in two parts form2html and form2js producing 2 files
 * - use string templates to generate Javascript
 * - use the HTML5Node type and the `str toString(HTML5Node x)` function to format to string
 * - use any client web framework (e.g. Vue, React, jQuery, whatever) you like for event handling
 * - map booleans to checkboxes, strings to textfields, ints to numeric text fields
 * - be sure to generate uneditable widgets for computed questions!
 * - if needed, use the name analysis to link uses to definitions
 */

void compile(AForm f) {
  writeFile(f.src[extension="js"].top, form2js(f));
  writeFile(f.src[extension="html"].top, "\<!doctype html\>\n" + toString(form2html(f))); 
}

HTML5Node form2html(AForm f) {
  // documentation is great, so grabbing filename this way
  // will break horribly if file structure is changed :)
  filename = src(f.src[extension="js"].top.path[10..]);
  
  HEAD = head([meta(charset("UTF-8")), title(f.name), script(filename)]);
  BODY = body(onload("ev(); updateVisibility();"),
  			p("Fill in the form and press submit to list the answers:"),
    		form([onsubmit("return false")] + [form2html(question) | question <- f.questions] +
    			[input(\type("submit"), \value("Submit"), onclick("onSubmit();"))]),
    		p(id("output"))
    	);
  return html([HEAD, BODY]);
}

HTML5Node form2html(AQuestion q) {
  switch(q){
  	case question(str question, AId identifier, AType t, list[AExpr] expr): {
  		divargs = [class("question")];
  		divargs += [question];
  		if(expr != []){
  			HTML5Node dv;
  			if(t.\type == "boolean"){
  			  dv = html5attr("data-value", "false");
  		  } else if (t.\type == "integer"){
  		    dv = html5attr("data-value", 0);
  		  } else if (t.\type == "string"){
  		    dv = html5attr("data-value", "");
  		  }
  		  	divargs += [span(id(identifier.name), html5attr("expr", escape_quotes(pretty_print(expr[0]))), dv, "0")];
  		} else {
  		  if(t.\type == "boolean"){
  			  divargs += [input(\type("checkbox"), id(identifier.name), onchange("ev(); updateVisibility();"))];
  		  } else if (t.\type == "integer"){
  		    divargs += [input(\type("number"), id(identifier.name), \value(0), onchange("ev(); updateVisibility();"))];
  		  } else if (t.\type == "string"){
  		    divargs += [input(\type("text"), id(identifier.name), \value(""), onchange("ev(); updateVisibility();"))];
  		  }
  		}
  		return div(divargs);
  	}
  	case cond(AExpr c, list[AQuestion] \if, list[AQuestion] \else): {
  		return div([class("conditition")] + [form2html(h) | h <- \if] + [form2html(h) | h <- \else]);
  	}
  };
}

str pretty_print(AExpr c){
	switch(c){
		case brackets(AExpr ex): return "(<pretty_print(ex)>)";
		case not(AExpr ex): return "!" + "(<pretty_print(ex)>)";
		case divide(AExpr ex1, AExpr ex2): return "(<pretty_print(ex1)>) / (<pretty_print(ex2)>)";
		case multiply(AExpr ex1, AExpr ex2): return "(<pretty_print(ex1)>) * (<pretty_print(ex2)>)";
		case add(AExpr ex1, AExpr ex2): return "(<pretty_print(ex1)>) + (<pretty_print(ex2)>)";
		case subtract(AExpr ex1, AExpr ex2): return "(<pretty_print(ex1)>) - (<pretty_print(ex2)>)";
		case less(AExpr ex1, AExpr ex2): return "(<pretty_print(ex1)>) \< (<pretty_print(ex2)>)";
		case gtr(AExpr ex1, AExpr ex2): return "(<pretty_print(ex1)>) \> (<pretty_print(ex2)>)";
		case leq(AExpr ex1, AExpr ex2): return "(<pretty_print(ex1)>) \<= (<pretty_print(ex2)>)";
		case geq(AExpr ex1, AExpr ex2): return "(<pretty_print(ex1)>) \>= (<pretty_print(ex2)>)";
		case eq(AExpr ex1, AExpr ex2): return "(<pretty_print(ex1)>) == (<pretty_print(ex2)>)";
		case neq(AExpr ex1, AExpr ex2): return "(<pretty_print(ex1)>) != (<pretty_print(ex2)>)";
		case and(AExpr ex1, AExpr ex2): return "(<pretty_print(ex1)>) && (<pretty_print(ex2)>)";
		case or(AExpr ex1, AExpr ex2): return "(<pretty_print(ex1)>) || (<pretty_print(ex2)>)";
		case ref(AId id): return "(getValue(\"<id.name>\"))";
		case integer(int n): {
			
			return intToStr(n);		
			//return toString(n);
			// toString(1) seems to bug out, defining own function
		}
		case boolean(str \bool): return \bool;
	}
}

str intToStr(int n){
	if(n >= 10){
		return intToStr(n / 10) + intToStr(n % 10);
	}
	if(n == 0){
		return "0";
	}
	if(n == 1){
		return "1";
	}
	if(n == 2){
		return "2";
	}
	if(n == 3){
		return "3";
	}
	if(n == 4){
		return "4";
	}
	if(n == 5){
		return "5";
	}
	if(n == 6){
		return "6";
	}
	if(n == 7){
		return "7";
	}
	if(n == 8){
		return "8";
	}
	if(n == 9){
		return "9";
	}
	return "";
}

str escape_quotes(str code){
	str result = "";
	for(i<-[0..size(code)]){
		if(code[i] == "\""){
			result += "&quot;";
		} else {
			result += code[i];
		}
	}
	return result;
}

str form2js(AForm f) {	
	return "<gen_ids(f)>
	'<on_submit(f)>
	'<evaluate()>
	'<evaluateOnce()> 
	'<recalculate()> 
	'<get_value()>
	'<update_visibility(f)>";
}

//- global list of question ids
str gen_ids(AForm f){
	ids = "var ids = [";
	for(/question(_, id, _, _) := f){
		ids += "\"" + id.name + "\"" + ",";
	}
	return ids + "];\n";
}

str on_submit(AForm f){
	result = "function onSubmit(){
	'	var result = \"\";
	'	for(var i in ids){
	'		var em = document.getElementById(ids[i]);
	'		// handle computed questions before normal questions
	'		if(em.hasAttribute(\"data-value\") && em.visible){
	'			result += ids[i] + \" : \" + em.getAttribute(\"data-value\") + \"\\n\";
	'		} else if(em.type == \"checkbox\"){
  	'			result += ids[i] + \" : \" + em.checked + \"\\n\"
	'		} else if((! em.hasAttribute(\"class\")) && em.visible){
	'			result += ids[i] + \" : \" + getValue(ids[i]) + \"\\n\";
	'		}
	'	}
	'	document.getElementById(\"output\").innerHTML = result;
	'}\n";
	return result;
}

str evaluate(){
	return "function ev(){
		'	var r = evOnce();
		'	var s;
		'	while(true){
		'		s = evOnce();
		'		if(r == s){
		'			break;
		'		} 
		'		r = s;
		'	}
		'	return r;
		'}\n";
}

str evaluateOnce(){ 
	return "function evOnce(){
		'	var result = \"\";
		'	for(var i in ids){
		'		result += ids[i] + \" : \" + recalculate(ids[i]) + \"\\n\";
		'	}
		'	return result;
		'}\n";
}

str recalculate(){
	return "function recalculate(id){
		'	var em = document.getElementById(id);
		'	if(em.hasAttribute(\"expr\")) {
		'		var value = eval(em.getAttribute(\"expr\"));
		'		em.setAttribute(\"data-value\", value);
		'		em.innerHTML = value;
		'		return value;
		'	}
		'	return getValue(id);
		'}\n";
}

str get_value(){
	return "function getValue(id){
		'	em = document.getElementById(id);
		'	if(em.hasAttribute(\"data-value\")){
		'		return em.getAttribute(\"data-value\");
		'	} else if(em.hasAttribute(\"type\") && em.type == \"checkbox\"){
		'		return em.checked;
		'	} else {
		'		return em.value;
		'	}
		'}\n";
}

str update_visibility(AForm f){
	return "function updateVisibility(){
		'	// mark every element as not visible
		'	for(i in ids){
		'		document.getElementById(ids[i]).visible = false;
		'	}
		'
		'	// mark visible elements as visible
		'<visibilityHelper(f.questions)>
		'
		'	// hide invisible elements, show visible elements
		'	for(i in ids){
		'		var em = document.getElementById(ids[i]);
		'		if(em.visible){
		'			if(em.parentElement.hasAttribute(\"hidden\")){
		'				em.parentElement.removeAttribute(\"hidden\");
		'			}
		'		} else {
		'			em.parentElement.setAttribute(\"hidden\", \"true\");
		'		}
		'	}
		'}\n";
}


str visibilityHelper(list[AQuestion] li){
	result = "";
	for(q <- li){
		switch(q){
			case cond(AExpr c, list[AQuestion] \if, list[AQuestion] \else): {
				result += "if ( eval(<pretty_print(c)>)) {
  					'<visibilityHelper(\if)>
  					'}\n";
  				if(\else != []){
  					result += "else {
  						'<visibilityHelper(\else)>
  						'}";	
  				}
  			}
  			case question(str question, AId identifier, AType t, list[AExpr] expr): {
  				result += "document.getElementById(\"<identifier.name>\").visible = true;\n";
  			} 
  			default :;
		};
	}
	return result;
}