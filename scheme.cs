////////////////////////////////////////////////////////////////
// An implementation of a subset of the Scheme programming language in C#.
// Scheme is a statically-bound dialect of Lisp.
// It features functions as first-class objects.
// (Functions can be arguments to and values of function calls.)	
// You have my permission to use this code however you like.
// Rex Dwyer
// June 2015
// rex.dwyer@pobox.com
////////////////////////////////////////////////////////////////

using System;
using System.IO;
using System.Text.RegularExpressions;
using System.Reflection;

// S-expressions are the fundamental data structures of Scheme.
// An S-expression can be either an atom or a list.
// Lists are made of cons-cells.  Cons-cells have a car and a cdr.
// The atom "nil" also represents the empty list.
abstract class Sexpr {
  public virtual Cons cons(Sexpr exp) {
    return new Cons(this, exp);
  }

  // car, cdr, second, third, and fourth are only defined for lists.
  // However we can avoid a whole lot of casting if we define them
  // for all Sexprs.
  public virtual Sexpr car() {
    System.Environment.Exit(-1);
    return null;
  }
  public virtual Sexpr cdr() {
    System.Environment.Exit(-1);
    return null;
  }
  public virtual Sexpr second() { 
    System.Environment.Exit(-1);
    return null;
  }

  public virtual Sexpr third() { 
    System.Environment.Exit(-1);
    return null;
  }

  public virtual Sexpr fourth() { 
    System.Environment.Exit(-1);
    return null;
  }

  public Sexpr evaluate() {
    return eval(Primitives.primitiveEnvironment());
  }

  public abstract Sexpr eval(Sexpr env);
  public abstract Sexpr evlis(Sexpr env);

  // isNil is overridden for the nil atom.
  public virtual bool isNil() {
    return false;
  }

  public abstract bool eq(Sexpr other);
  public abstract string asString();

}

////////////////

// This class implements atoms.  Atoms are identifiers or numbers.
abstract class Atom: Sexpr {
  public override Sexpr evlis(Sexpr env) {
    return eval(env);  // This should never be anything but nil.
  }
}

////////////////

class Ident: Atom {
  public string name;
  public Ident(string name) {
    this.name = name;
  }

  public override bool isNil() {
    return name == "nil";
  }

  // Identifiers are only equal to other identifiers with the same name.
  public override bool eq(Sexpr other) {
    if (other is Ident) return name == ((Ident) other).name;
    else return false;
  }

  public override string asString() {
    return name;
  }
  
  public override Sexpr eval(Sexpr env) {
    Sexpr e, vars, vals;
    for (e = env; !e.isNil(); e = e.cdr()) {
      // for each variable on rib...
      vars = e.car().car();
      vals = e.car().cdr();
      while (!vars.isNil()) {
	if (name == ((Ident)vars.car()).name) return vals.car();
	vars = vars.cdr();
	vals = vals.cdr();
      }	       
    }
    System.Environment.Exit(-1);
    return null;
  }
}

////////////////

class Number: Atom {
  public int value;

  // A number evaluates to itself.
  public Number(int value) {
    this.value = value;
  }

  public override Sexpr eval(Sexpr env) {
    return this;
  }

  public override string asString() {
    return value.ToString();
  }

  // Numbers are only equal to other numbers with the same value.
  public override bool eq(Sexpr other) {
    if (other is Number) return value == ((Number)other).value;
    else return false;
  }
}

////////////////

// Cons cells represent lists and have a car and cdr.
class Cons: Sexpr {
  public Sexpr kar, kdr;
  public override Sexpr car() {
    return kar;
  }
  public override Sexpr cdr() {
    return kdr;
  }

  public Cons(Sexpr car, Sexpr cdr) {
    this.kar = car;
    this.kdr = cdr;
  }
  
  // The second, third, and fourth elements of a list.
  public override Sexpr second() { 
    return cdr().car();
  }

  public override Sexpr third() { 
    return cdr().cdr().car();
  }

  public override Sexpr fourth() { 
    return cdr().cdr().cdr().car();
  }

  public override bool eq(Sexpr other) {
    return false;
  }

  public override string asString() {
    string s = "(" + car().asString();
    for (Sexpr sexpr = cdr(); !sexpr.isNil(); sexpr = sexpr.cdr()) {
      s += " " + sexpr.car().asString();
    }
    s += ")";
    return s;
  }

  // The meat of the interpreter.
  public override Sexpr eval(Sexpr env) {
    //System.Console.Out.WriteLine(asString());
    // Check for special forms: quote, list, prog2, if, lambda, letrec.
    if (car() is Ident) {
      string form = ((Ident)car()).name;
      if (form == "quote") {
	return second();
      }
      if (form == "list") {
	return cdr().evlis(env);
      }
      if (form == "prog2") {
	second().eval(env);
	return third().eval(env);
      }
      if (form == "if") {
        Sexpr test = second().eval(env);
	if (test.isNil()) {
	  return fourth().eval(env);
	}
	else {
	  return third().eval(env);
	}
      }
      if (form == "lambda") { // Build a closure of function definition and current environment.
	return new Ident("*CLOSURE*").cons(cons(env.cons(new Ident("nil"))));
      }
      if (form == "letrec") {
	// The new environment will include the new functions, and the
	// new functions will include the new environment.  Therefore, we
	// have to build a circular structure.
	// The environment is a backbone that is a list of vertebrae.
	// Each vertebra holds two ribs:
	// One for function names and one for closures.
	// The ribs get filled in later.
	Sexpr nyl = new Ident("nil");
	Cons vertebra = nyl.cons(nyl);
	Sexpr newenv = vertebra.cons(env);
	Sexpr names = nyl;
	Sexpr vals = nyl;
	// Now step through the function definitions and build up a
	// list of names and a list of closures.
	for (Sexpr pairs = second(); !pairs.isNil(); pairs = pairs.cdr()) {
	  Sexpr pair = pairs.car();
	  Sexpr name = pair.car();
	  Sexpr val = pair.second().eval(newenv); // close lambda
	  names = name.cons(names);
	  vals = val.cons(vals);
	}
	vertebra.kar = names;
	vertebra.kdr = vals;
	// Last, evaluate the body of the letrec 
	// in the new extended environment.
	return third().eval(newenv);
      }
    }
    // The only remaining possibility is a function application.
    // We have to evaluate everything in the list to find the function
    // definition and the actual arguments, then either evaluate a primitive
    // function like car or cons, or evaluate a user-defined function.
    return ((Cons)evlis(env)).apply();
  }

  // Evaluate each of a list of expression in the current environment.
  // Return a list of the results.
  public override Sexpr evlis(Sexpr env) {
    return new Cons(kar.eval(env), kdr.evlis(env));
  }

  // apply a function to actual arguments.
  public Sexpr apply() {
    Sexpr fun = kar;
    Sexpr args = kdr;
    if (fun is Atom) {
    	return Primitives.invokePrimitive(((Ident)fun).name,args);
    }
    if (((Ident) fun.car()).name == "*CLOSURE*") {
      // Get formal parameters, body of function, and static environment
      // from the closure.
      Sexpr lambda = fun.second();
      Sexpr formals = lambda.second();
      Sexpr body = lambda.third();
      Sexpr env = fun.third();
      // Create new pair of ribs for the environment.
      Sexpr vetebra = formals.cons(args);
      Sexpr newenv = vetebra.cons(env);
      // Evaluate body in new environment.
      return body.eval(newenv);
    }
    // This shouldn't happen.
    System.Environment.Exit(-1);
    return null;
  }
}

////////////////////////////////////////////////////////////////

// This class implements the primitive functions car, cdr, cons, etc.
class Primitives {


  // This constructs an environment that make the atom representing
  // primitives map to themselves.
  public static Sexpr primitiveEnvironment() {
    string nameString = "(t nil car cdr cons atom null " + 
      "+ - * / == > < not and or print)";
    Sexpr names = (new Parser(new StringReader(nameString))).parse();
    string valString = "(t nil car cdr cons atom isNil " + 
      "plus minus times div eq greater less not and or print)";
    Sexpr vals = (new Parser(new StringReader(valString))).parse();
    return (names.cons(vals)).cons(new Ident("nil"));
  }

  // This function implements the primitives using reflection.
  // We search for a method with the name of the primitive in the
  // Primitives class, then invoke the method.
  public static Sexpr invokePrimitive(string name, Sexpr args) {
    MethodInfo method = typeof (Primitives).GetMethod(name);
    Object[] obj = new Object[1];
    obj[0] = args;
    return (Sexpr) method.Invoke(null,obj);
  }


  // The primitive methods follow:
  public static Sexpr car(Sexpr args) {
    return args.car().car();
  }

  public static Sexpr cdr(Sexpr args) {
    return args.car().cdr();
  }

  // implements null
  public static Sexpr isNil(Sexpr args) {
    return args.car().isNil() ? new Ident("t") : new Ident("nil");
  }

  public static Sexpr atom(Sexpr args) {
    return (args.car() is Atom) ? new Ident("t") : new Ident("nil");
  }

  public static Sexpr not(Sexpr args) {
    return args.car().isNil() ? new Ident("t") : new Ident("nil");
  }

  public static Sexpr print(Sexpr args) {
    System.Console.Out.WriteLine(args.car().asString());
    return args.car();
  }

  public static Sexpr cons(Sexpr args) {
    return args.car().cons(args.second());
  }

  public static Sexpr and (Sexpr args) {
    return args.car().isNil() ? args.car() : args.second();
  }

  public static Sexpr or (Sexpr args) {
    return !args.car().isNil() ? args.car() : args.second();
  }

  // implements ==
  public static Sexpr eq (Sexpr args) {
    return args.car().eq(args.second()) ? new Ident("t") : new Ident("nil");
  }

  // implements +
  public static Sexpr plus (Sexpr args) {
    int num1 = ((Number) args.car()).value;
    int num2 = ((Number) args.second()).value;
    return new Number(num1 + num2);
  }

  // implements -
  public static Sexpr minus (Sexpr args) {
    int num1 = ((Number) args.car()).value;
    int num2 = ((Number) args.second()).value;
    return new Number(num1 - num2);
  }

  // implements *
  public static Sexpr times (Sexpr args) {
    int num1 = ((Number) args.car()).value;
    int num2 = ((Number) args.second()).value;
    return new Number(num1 * num2);
  }

  // implements /
  public static Sexpr div (Sexpr args) {
    int num1 = ((Number) args.car()).value;
    int num2 = ((Number) args.second()).value;
    return new Number(num1 / num2);
  }

  // implements <
  public static Sexpr less (Sexpr args) {
    int num1 = ((Number) args.car()).value;
    int num2 = ((Number) args.second()).value;
    return (num1 < num2) ? new Ident("t") : new Ident("nil");
  }

  // implements >
  public static Sexpr greater (Sexpr args) {
    int num1 = ((Number) args.car()).value;
    int num2 = ((Number) args.second()).value;
    return (num1 > num2) ? new Ident("t") : new Ident("nil");
  }
}

////////////////////////////////////////////////////////////////
// Parses one s-expression from a TextReader.
class Parser {
  TextReader tr;

  public Parser(TextReader tr) {
    this.tr = tr;
  }
  
  // Consumes white space.
  public void skipWhite() {
    char c = (char) tr.Peek();
    while (c == ' ' || c == '\n' || c == '\r' || c == '\t') {
      tr.Read();
      c = (char) tr.Peek();
    }
  }
  
  // Parse a Sexpr.
  public Sexpr parse() {
    skipWhite();
    char c = (char) tr.Peek();
    if (c == '(') {   
      tr.Read();
      return parseCdr();
    }
    return parseAtom();
  }

  // Parses what's level of a list when the ( is removed.
  public Sexpr parseCdr() {
    skipWhite();
    char c = (char) tr.Peek();
    if (c == ')') { // done with this liet
      tr.Read();
      return new Ident("nil");
    } 
    else { // parse the current expression, then the rest of the list.
      return parse().cons(parseCdr());
    }
  }

  // Parses an atom and creates a record.  
  // Identifiers can contain most characters that are not white space or a paren.
  public Sexpr parseAtom() {
    skipWhite();
    string s = "";
    string regexp = "[A-Za-z0-9<=>?_=*/+-]";
    while (Regex.Match(((char) tr.Peek()).ToString(), regexp).Success) {
      s += (char) tr.Read();
    }
    int val;
    bool isInt = System.Int32.TryParse(s, out val);
    if (isInt) return new Number(val);
    else return new Ident(s);
  }
}

////////////////////////////////////////////////////////////////
// main program.

class Program {
  static void Main(string[] args) {
    Parser parser = new Parser(System.Console.In);
    Sexpr prog = parser.parse();
    System.Console.Out.WriteLine(prog.asString());
    Sexpr result = prog.evaluate();
    System.Console.Out.WriteLine(result.asString());
  }
}     
