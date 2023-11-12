import Assign3.Parser.Parser
import Assign3.Syntax.Syntax._
import Assign3.Typer.Typer
import scala.collection.immutable.ListMap

object Fish {

  // ======================================================================
  // Capture-avoiding substitution
  // ======================================================================

  val generator = SymGenerator()

  object SubstExpr extends Substitutable[Expr] {
    // swap y and z in e
    def swap(e: Expr, y: Variable, z: Variable): Expr =
      def go(e: Expr): Expr = e match {
        // Value must be closed
        case v: Value => v

        case Unit => Unit

        case Num(n) => Num(n)
        case Plus(e1, e2) => Plus(go(e1), go(e2))
        case Minus(e1, e2) => Minus(go(e1), go(e2))
        case Times(e1, e2) => Times(go(e1), go(e2))

        case Bool(b) => Bool(b)
        case Eq(e1, e2) => Eq(go(e1), go(e2))
        case IfThenElse(e, e1, e2) => IfThenElse(go(e), go(e1), go(e2))

        case Str(s) => Str(s)
        case Length(e) => Length(go(e))
        case Index(e1, e2) => Index(go(e1), go(e2))
        case Concat(e1, e2) => Concat(go(e1), go(e2))

        case Var(x) => Var(swapVar(x,y,z))
        case Let(x,e1,e2) => Let(swapVar(x,y,z),go(e1),go(e2))

        case Pair(e1,e2) => Pair(go(e1),go(e2))
        case First(e) => First(go(e))
        case Second(e) => Second(go(e))

        case Lambda(x,e) => Lambda(swapVar(x,y,z),go(e))
        case Apply(e1,e2) => Apply(go(e1),go(e2))
        case Rec(f,x,e) => Rec(swapVar(f,y,z), swapVar(x,y,z), go(e))

        case Record(es) => Record(es.map((x, e) => (x, go(e))))
        case Proj(e, l) => Proj(go(e), l)

        case Ref(e) => Ref(go(e))
        case Deref(e) => Deref(go(e))
        case Assign(e1, e2) => Assign(go(e1), go(e2))

        case Sequ(e1, e2) => Sequ(go(e1),go(e2))
        case LetPair(x1,x2,e1,e2) =>
          LetPair(swapVar(x1,y,z),swapVar(x2,y,z),go(e1),go(e2))
        case LetFun(f,x,e1,e2) =>
          LetFun(swapVar(f,y,z),swapVar(x,y,z),go(e1),go(e2))
        case LetRec(f,x,e1,e2) =>
          LetRec(swapVar(f,y,z),swapVar(x,y,z),go(e1),go(e2))
        case LetRecord(xs,e1,e2) =>
          LetRecord(xs.map((l,x) => (l, swapVar(x,y,z))),go(e1),go(e2))
        }
      go(e)

    ////////////////////
    // EXERCISE 4     //
    ////////////////////
    def apply(theta: Subst[Expr], e: Expr): Expr = {
      // BEGIN ANSWER
      e match {
        // Arithmetic expressions
        case Num(n: Integer) => Num(n)
        case Plus(e1: Expr, e2: Expr) => Plus(apply(theta, e1), apply(theta, e2))
        case Minus(e1: Expr, e2: Expr) => Minus(apply(theta, e1), apply(theta, e2))
        case Times(e1: Expr, e2: Expr) => Times(apply(theta, e1), apply(theta, e2))

        // Strings
        case Str(s: String) => Str(s)
        case Length(e: Expr) => Length(apply(theta, e))
        case Index(e1: Expr, e2: Expr) => Index(apply(theta, e1), apply(theta, e2))
        case Concat(e1: Expr, e2: Expr) => Concat(apply(theta, e1), apply(theta, e2))

        // Booleans
        case Bool(b: Boolean) => Bool(b)
        case Eq(e1: Expr, e2: Expr) => Eq(apply(theta, e1), apply(theta, e2))
        case IfThenElse(e1: Expr, e2: Expr, e3: Expr) => IfThenElse(apply(theta, e1), apply(theta, e2), apply(theta, e3))

        // Variables and let-binding
        case Var(x: Variable) => {
          if theta.contains(x) then theta(x)
          else Var(x)
        }
        case Let(y: Variable, e1: Expr, e2: Expr) => {
          val z = generator.genVar(y)
          Let(z, apply(theta, e1), apply(theta, swap(e2, y, z)))
        }

        // Functions
        case Lambda(y: Variable, e0: Expr) => {
          val z = generator.genVar(y)
          Lambda(z, apply(theta, swap(e0, y, z)))
        }
        case Apply(e1: Expr, e2: Expr) => Apply(apply(theta, e1), apply(theta, e2))
        case Rec(f: Variable, y: Variable, e0: Expr) => {
          val g = generator.genVar(f)
          val z = generator.genVar(y)
          Rec(g, z, apply(theta, swap(swap(e0, f, g), y, z)))
        }

        // Pairing
        case Pair(e1: Expr, e2: Expr) => Pair(apply(theta, e1), apply(theta, e2))
        case First(e1: Expr) => First(apply(theta, e1))
        case Second(e1: Expr) => Second(apply(theta, e1))

        // Records
        case Record(es: Field[Expr]) => {
          var new_es = ListMap[Label, Expr]()
          for ((label, exp) <- es) {
            new_es = new_es + (label -> apply(theta, exp))
          }

          return Record(new_es)
        }
        case Proj(e1: Expr, l: Label) => Proj(apply(theta, e1), l)

        // References
        case Ref(e1: Expr) => Ref(apply(theta, e1))
        case Deref(e1: Expr) => Deref(apply(theta, e1))
        case Assign(e1: Expr, e2: Expr) => Assign(apply(theta, e1), apply(theta, e2))

        case _ => {
          println(e)
          sys.error("expression not valid for substitution")
        }
      }
      // END ANSWER
    }

  }
  import SubstExpr.{subst, ra2AppAssoc, ra2CompAssoc}

  // ======================================================================
  // Desugaring
  // ======================================================================

  ////////////////////
  // EXERCISE 5     //
  ////////////////////

  def desugar(e: Expr): Expr = e match {
    // Value
    case v: Value => sys.error("desugar: there should be no value at the desugar stage")

    // Arithmetic expressions
    case Num(n: Integer) => e
    case Plus(e1: Expr, e2: Expr) => Plus(desugar(e1), desugar(e2))
    case Minus(e1: Expr, e2: Expr) => Minus(desugar(e1), desugar(e2))
    case Times(e1: Expr, e2: Expr) => Times(desugar(e1), desugar(e2))

    // Booleans
    case Bool(b: Boolean) => e
    case Eq(e1: Expr, e2: Expr) => Eq(desugar(e1),desugar(e2))
    case IfThenElse(cond: Expr, e1: Expr, e2: Expr) => IfThenElse(desugar(cond), desugar(e1), desugar(e2))

    // Strings
    case Str(s: String) => e
    case Length(e: Expr) => Length(desugar(e))
    case Index(e1: Expr, e2: Expr) => Index(desugar(e1), desugar(e2))
    case Concat(e1: Expr, e2: Expr) => Concat(desugar(e1), desugar(e2))

    // Variables and let-binding
    case Let(x: Variable, e1: Expr, e2: Expr) => Let(x, desugar(e1), desugar(e2))
    case Var(x: Variable) => e

    // Functions
    case Lambda(x: Variable, e1: Expr) => Lambda(x, desugar(e1))
    case Apply(e1: Expr, e2: Expr) => Apply(desugar(e1), desugar(e2))
    case Rec(f: Variable, x: Variable, e1: Expr) => Rec(f, x, desugar(e1))

    // Pairing
    case Pair(e1: Expr, e2: Expr) => Pair(desugar(e1), desugar(e2))
    case First(e1: Expr) => First(desugar(e1))
    case Second(e1: Expr) => Second(desugar(e1))

    // Records
    case Record(es: Field[Expr]) => {
      var new_es = ListMap[Label, Expr]()
      for ((label, exp) <- es) {
        new_es = new_es + (label -> desugar(exp))
      }
      Record(new_es)
    }
    case Proj(e1: Expr, l: Label) => Proj(desugar(e1), l)

    // References
    case Ref(e1: Expr) => Ref(desugar(e1))
    case Deref(e1: Expr) => Deref(desugar(e1))
    case Assign(e1: Expr, e2: Expr) => Assign(desugar(e1), desugar(e2))

    // Syntactic sugars
    case LetFun(f: Variable, x: Variable, e1: Expr, e2: Expr) => Let(f, Lambda(x, desugar(e1)), desugar(e2))
    case LetRec(f: Variable, x: Variable, e1: Expr, e2: Expr) => Let(f, Rec(f, x, desugar(e1)), desugar(e2))
    case LetPair(x: Variable, y: Variable, e1: Expr, e2: Expr) => {
      val p = generator.genVar("p")
      var theta: Subst[Expr] = ListMap[Variable, Expr](x -> First(Var(p)), y -> Second(Var(p)))
      Let(p, desugar(e1), desugar(SubstExpr.apply(theta, e2)))
    }
    case LetRecord(xs: Field[Variable], e1: Expr, e2: Expr) => {
      val r = generator.genVar("r")
      var theta: Subst[Expr] = ListMap[Variable, Expr]()
      for ((label, x) <- xs) {
        theta = theta + (x -> Proj(Var(r), label))
      }

      Let(r,
          desugar(e1),
          desugar(SubstExpr.apply(theta, e2))
        )
    }
    case Sequ(e1: Expr, e2: Expr) => {
      val x = generator.genVar("x")
      Let(x, desugar(e1), desugar(e2))
    }

    case _ => sys.error("desugar: not implemented")
  }


  // ======================================================================
  // Primitive operations
  // ======================================================================

  object Value {
    // utility methods for operating on values
    def add(v1: Value, v2: Value): Value = (v1, v2) match
      case (NumV(v1), NumV(v2)) => NumV (v1 + v2)
      case _ => sys.error("arguments to addition are non-numeric")

    def subtract(v1: Value, v2: Value): Value = (v1, v2) match
      case (NumV(v1), NumV(v2)) => NumV (v1 - v2)
      case _ => sys.error("arguments to subtraction are non-numeric")

    def multiply(v1: Value, v2: Value): Value = (v1, v2) match
      case (NumV(v1), NumV(v2)) => NumV (v1 * v2)
      case _ => sys.error("arguments to multiplication are non-numeric")

    def eq(v1: Value, v2: Value): Value = (v1, v2) match
      case (NumV(v1), NumV(v2)) => BoolV (v1 == v2)
      case (BoolV(v1), BoolV(v2)) => BoolV (v1 == v2)
      case (StringV(v1), StringV(v2)) => BoolV (v1 == v2)
      case _ => sys.error("arguments to = are not base types")

    def length(v: Value): Value = v match
      case StringV(v1) => NumV(v1.length)
      case _ => sys.error("argument to length is not a string")

    def index(v1: Value, v2: Value): Value = (v1, v2) match
      case (StringV(v1), NumV(v2)) => StringV(v1.charAt(v2).toString)
      case _ => sys.error("arguments to index are not valid")

    def concat(v1: Value, v2: Value): Value = (v1, v2) match
      case (StringV(v1), StringV(v2)) => StringV(v1 ++ v2)
      case _ => sys.error("arguments to concat are not strings")
  }


  // ======================================================================
  // Evaluation
  // ======================================================================


  ////////////////////
  // EXERCISE 6     //
  ////////////////////
  def eval (e : Expr): Value = e match {
    // Value
    case v: Value => v

    // Unit
    case Unit => UnitV

    // Integers
    case Num(n: Integer) => NumV(n)
    case Plus(e1: Expr, e2: Expr) => Value.add(eval(e1), eval(e2))
    case Minus(e1: Expr, e2: Expr) => Value.subtract(eval(e1), eval(e2))
    case Times(e1: Expr, e2: Expr) => Value.multiply(eval(e1), eval(e2))

    // Booleans
    case Bool(b: Boolean) => BoolV(b)
    case Eq(e1: Expr, e2:Expr) => Value.eq(eval(e1), eval(e2))
    case IfThenElse(e: Expr, e1: Expr, e2: Expr) => {
      if eval(e) == BoolV(true) then eval(e1)
      else eval(e2)
    }

    // Strings
    case Str(s: String) => StringV(s)
    case Length(e1: Expr) => Value.length(eval(e1))
    case Index(e1: Expr, e2: Expr) => Value.index(eval(e1), eval(e2))
    case Concat(e1: Expr, e2: Expr) => Value.concat(eval(e1), eval(e2))

    // Let-binding
    case Let(x: Variable, e1: Expr, e2: Expr) => {
      val v1 = eval(e1)
      val theta: Subst[Expr] = ListMap[Variable, Expr](x -> v1)
      eval(SubstExpr.apply(theta, e2))
    }

    // Functions
    case Lambda(x: Variable, e: Expr) => FunV(x, e)
    case Rec(f: Variable, x: Variable, e: Expr) => RecV(f, x, e)

    case Apply(e1: Expr, e2: Expr) => {
      eval(e1) match {
        case FunV(x: Variable, e: Expr) => {
          val v1 = eval(e2)
          val theta: Subst[Expr] = ListMap[Variable, Expr](x -> v1)
          eval(SubstExpr.apply(theta, e))
        }
        case RecV(f: Variable, x: Variable, e: Expr) => {
          val v1 = eval(e2)
          val theta: Subst[Expr] = ListMap[Variable, Expr](x -> v1, f -> e)
          eval(SubstExpr.apply(theta, e))
        }
      }
    }

    // Pairing
    case Pair(e1: Expr, e2: Expr) => {
      val v1 = eval(e1)
      val v2 = eval(e2)
      PairV(v1, v2)
    }
    case First(e1: Expr) => {
      val res = eval(e1)
      res match {
        case PairV(v1: Value, v2: Value) => v1
        case _ => sys.error("Unable to evaluate pair")
      }
    }
    case Second(e1: Expr) => {
      val res = eval(e1)
      res match {
        case PairV(v1: Value, v2: Value) => v2
        case _ => sys.error("Unable to evaluate pair")
      }
    }

    // Records
    case Record(es: Field[Expr]) => {
      var record: Field[Value] = ListMap[Label, Value]()
      for ((label, expr) <- es) {
        record = record + (label -> eval(expr))
      }
      RecordV(record)
    }
    case Proj(e: Expr, l: Label) => {
      val res = eval(e)
      res match {
        case RecordV(vs: Field[Value]) => {
          if vs.contains(l) then vs(l)
          else sys.error("No label found")
        }
        case _ => sys.error("Unable to evaluate record")
      }
    }

    // References
    case Ref(e: Expr) => {
      val v = eval(e)
      val ref_cell_val = RefCell[Value](v)
      Cell(ref_cell_val)
    }
    case Deref(e: Expr) => {
      eval(e) match {
        case Cell(ref_cell_val) => ref_cell_val.get
      }
    }
    case Assign(e1: Expr, e2: Expr) => {
      eval(e1) match {
        case Cell(ref_cell_val) => {
          ref_cell_val.set(eval(e2))
          UnitV
        }
      }
    }

    case Var(_) => sys.error("Should not be evaluated")
    case LetPair(_, _, _, _) => sys.error("Should have been desugared")
    case LetFun(_, _, _, _) => sys.error("Should have been desugared")
    case LetRec(_, _, _, _) => sys.error("Should have been desugared")
    case LetRecord(_, _, _) => sys.error("Should have been desugared")
    case Sequ(_, _) => sys.error("Should have been desugared")

  }

  // END ANSWER

  /////////////////////////////////////////////////////////
  // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! //
  // THE REST OF THIS FILE SHOULD NOT NEED TO BE CHANGED //
  // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! //
  /////////////////////////////////////////////////////////
  
  // ======================================================================
  // Some simple programs
  // ======================================================================

  // The following examples illustrate how to embed Fish source code into
  // Scala using multi-line comments, and parse it using parser.parseStr.

  // Example 1: the swap function
  def example1: Expr = parser.parseStr("""
    let swap = \ x . (snd(x), fst(x)) in
    swap(42,17)
    """)

  val parser = new Parser

  // ======================================================================
  // Main
  // ======================================================================

  object Main {
    def typecheck(ast: Expr):Type =
      Typer.tyOf(ListMap(),ast)._1;

    def evaluate(ast: Expr):Value =
      eval(ast)

    def showResult(ast: Expr) = {
      println("AST:  " + ast.toString + "\n")

      try {
        print("Type Checking...");
        val ty = typecheck(ast);
        println("Done!");
        println("Type of Expression: " + ty.toString + "\n") ;
      } catch {
          case e:Throwable => println("Error: " + e)
      }
      try {
        println("Desugaring...");
        val core_ast = desugar(ast);
        println("Done!");
        println("Desugared AST: " + core_ast.toString + "\n") ;

        println("Evaluating...");
        println("Result: " + evaluate(core_ast))
      } catch {
        case e:Throwable => {
          println("Error: " + e)
          println("Evaluating raw AST...");
          println("Result: " + evaluate(ast))
        }
      }
    }

    def start(): Unit = {
      println("Welcome to Fish! (V1.0, October 9, 2023)");
      println("Enter expressions to evaluate, :load <filename.fish> to load a file, or :quit to quit.");
      println("This REPL can only read one line at a time, use :load to load larger expressions.");
      repl()
    }

    def repl(): Unit = {
      print("Fish> ");
      val input = scala.io.StdIn.readLine();
      if(input == ":quit") {
        println("Goodbye!")
      }
      else if (input.startsWith(":load")) {
        try {
          val ast = parser.parse(input.substring(6));
          showResult(ast)
        } catch {
          case e:Throwable => println("Error: " + e)
        }
        repl()
      } else {
        try {
          val ast = parser.parseStr(input);
          showResult(ast)
        } catch {
          case e:Throwable => println("Error: " + e)
        }
        repl()
      }
    }
  }

  def main( args:Array[String] ):Unit = {
    if(args.length == 0) {
      Main.start()
    } else {
      try {
        print("Parsing...");
        val ast = parser.parse(args.head)
        println("Done!");
        Main.showResult(ast)
      } catch {
        case e:Throwable => println("Error: " + e)
      }
    }
  }

}
