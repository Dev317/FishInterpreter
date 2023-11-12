package Assign3.Parser

import Assign3.Syntax.Syntax._
import scala.collection.immutable.ListMap
import scala.collection.immutable.Set
import scala.util.parsing.combinator.PackratParsers
import scala.util.parsing.combinator.syntactical.StandardTokenParsers

/*======================================================================
  The rest of this file is support code, which you should not (and do not
  need to) change.
  ====================================================================== */

class Parser extends StandardTokenParsers with PackratParsers {

  type P[+A] = PackratParser[A]

  def parseStr(input: String): Expr = {
    phrase(expression)(new lexical.Scanner(input)) match {
      case Success(ast, _) => ast
      case e: NoSuccess => sys.error(e.msg)
    }
  }

  def parse(input: String): Expr = {
    val source = scala.io.Source.fromFile(input)
    val lines = try source.mkString finally source.close()
    parseStr(lines)
  }

  lexical.reserved ++= List("let", "in", "rec", "if", "then", "else",
    "int", "str", "bool", "true", "false", "fst", "snd", "concat",
    "index", "length", "fun", "ref", "unit"
  )
  lexical.delimiters ++= List("=","*", "\\", "+", "-", "(", ")", "==", ":", ".",
    "->", ",", "<", ">", ":=", "!", ";"
  )

  lazy val expression: P[Expr] =
    simpleExpr

  lazy val lambda: P[Expr] =
    ("\\" ~> ident) ~ ("." ~> expression) ^^ {
      case arg~body => Lambda(arg, body)
    }

  lazy val rec: P[Expr] =
    ("rec" ~> ident) ~
      (("(" ~> ident) <~ ")") ~
      ("." ~> expression) ^^ {
        case recArg~funArg~body =>
          Rec(recArg, funArg, body)
      }

  lazy val ifExpr: P[Expr] =
    ("if" ~> expression) ~
      ("then" ~> expression) ~
      ("else" ~> expression) ^^ {
        case cond~e1~e2 => IfThenElse(cond,e1,e2)
      }

  lazy val letExpr: P[Expr] =
    ("let" ~> ident) ~ ("=" ~> expression) ~ ("in" ~> expression) ^^ {
      case binder~e1~e2 => Let(binder,e1,e2)
    }

  lazy val letFun: P[Expr] =
    ("let" ~ "fun" ~> ident) ~ ("(" ~> ident <~ ")") ~ ("=" ~> expression) ~
      ("in" ~> expression) ^^ {
        case fun~binder~e1~e2 => LetFun(fun,binder,e1,e2)
      }

  lazy val letRec: P[Expr] =
    ("let" ~ "rec" ~> ident) ~ ("(" ~> ident <~ ")") ~ ("=" ~> expression) ~
      ("in" ~> expression) ^^ {
        case fun~binder~e1~e2 => LetRec(fun,binder,e1,e2)
      }

  lazy val letPair: P[Expr] =
    ("let" ~ "(") ~> ident ~ ("," ~> ident <~ ")") ~
      ("=" ~> expression) ~ ("in" ~> expression) ^^ {
        case x~y~e1~e2 => LetPair(x,y,e1,e2)
      }

  lazy val letRecord: P[Expr] =
    ("let" ~> recordPattern) ~
      ("=" ~> expression) ~ ("in" ~> expression) ^^ {
        case xs~e1~e2 => LetRecord(xs,e1,e2)
      }

  lazy val recordPattern: P[Field[Variable]] =
    "<" ~> recordPatternFields <~ ">" ^^ {
      case es => es
    } |
    "<" ~ ">" ^^ {
      case _~_ => ListMap()
    }

  lazy val recordPatternFields: P[Field[Variable]] =
    recordPatternElem ~ "," ~ recordPatternFields ^^ {
      case (l,e)~_~es => ListMap(l -> e) ++ es
    } |
    recordPatternElem ^^ {
      case (l, e) => ListMap(l -> e)
    }

  lazy val recordPatternElem: P[(Label, Variable)] =
    ident ~ "=" ~ ident ^^ {
      case l~_~e => (l, e)
    }

  lazy val assignExpr: P[Expr] =
    fact ~ ":=" ~ simplerExpr ^^ {
      case e1~_~e2 => Assign(e1, e2)
    }

  lazy val sequExpr: P[Expr] =
    expression ~ ";" ~ expression ^^ {
      case e1~_~e2 => Sequ(e1, e2)
    }

  lazy val typ: P[Type] =
    TyFunp

  lazy val TyFunp: P[Type] =
    TyPairp ~ "->" ~ TyFunp ^^ {
      case t1~_~t2 => TyFun(t1,t2)
    } | TyPairp

  lazy val TyPairp: P[Type] =
    primitiveType ~ "*" ~ TyPairp ^^ {
      case t1~_~t2 => TyPair(t1,t2)
    } | primitiveType

  lazy val primitiveType: P[Type] =
    "bool" ^^^ TyBool | "int" ^^^ TyInt | "str" ^^^ TyString |  "("~>typ<~")"

  lazy val operations: P[Expr] =
    application |
    projection |
    deref |
    ("fst" ~ "(") ~> expression <~ ")" ^^ (x => First(x)) |
    ("snd" ~ "(") ~> expression <~ ")" ^^ (x => Second(x)) |
    ("ref" ~ "(") ~> expression <~ ")" ^^ (x => Ref(x)) |
    ("length" ~ "(") ~> expression <~ ")" ^^ (x => Length(x)) |
    ("concat"  ~ "(") ~> expression ~ ("," ~> expression) <~ ")" ^^ {
      case e1~e2 => Concat(e1,e2)
    } |
    ("index" ~ "(") ~> expression ~ ("," ~> expression) <~ ")" ^^ {
      case e1~e2 => Index(e1,e2)
    }

  lazy val arith: P[Expr] =
    eq

  lazy val prod: P[Expr] =
    prod ~ "*" ~ fact ^^ {
      case e1~_~e2 => Times(e1,e2)
    } | fact

  lazy val summation: P[Expr] =
    summation ~ "+" ~ prod ^^ {
      case e1~_~e2 => Plus(e1,e2)
    } | summation ~ "-" ~ prod ^^ {
      case e1~_~e2 => Minus(e1,e2)
    } | prod

  lazy val eq: P[Expr] =
    simpleExpr ~ "==" ~ summation ^^ {
      case e1~_~e2 => Eq(e1,e2)
    } | summation

  lazy val application: P[Expr] =
    fact ~ fact ^^ {
      case e1~e2 => Apply(e1,e2)
    }

  lazy val projection: P[Expr] =
    fact ~ "." ~ ident ^^ {
      case e~_~l => Proj(e, l)
    }

  lazy val deref: P[Expr] =
    "!" ~> fact ^^ {e => Deref(e)}

  lazy val simplerExpr: P[Expr] = (
    lambda |
    rec |
    letExpr |
    letFun |
    letRec |
    letPair |
    letRecord |
    assignExpr |
    ifExpr |
    arith |
    fact
  )

  lazy val simpleExpr: P[Expr] = (
    sequExpr |
    simplerExpr
  )

  lazy val pairLit: P[Expr] =
    "(" ~> expression ~ "," ~ expression <~ ")" ^^ {
      case t1~_~t2 => Pair(t1,t2)
    }

  lazy val recordLit: P[Expr] =
    "<" ~> recordFields <~ ">" ^^ {
      case es => Record(es)
    } |
    "<" ~ ">" ^^ {
      case _~_ => Record(ListMap())
    }

  lazy val recordFields: P[Field[Expr]] =
    recordElem ~ "," ~ recordFields ^^ {
      case (l,e)~_~es => ListMap(l -> e) ++ es
    } |
    recordElem ^^ {
      case (l, e) => ListMap(l -> e)
    }

  lazy val recordElem: P[(Label, Expr)] =
    ident ~ "=" ~ expression ^^ {
      case l~_~e => (l, e)
    }


  lazy val fact: P[Expr] = (
    operations |
      recordLit |
      pairLit |
      (ident ^^ {x => Var(x)}) |
      (numericLit ^^ {x => Num(x.toInt) }) |
      (stringLit ^^ {s => Str(s)}) |
      ("true" ^^^ Bool(true)) |
      ("false" ^^^ Bool(false)) |
      ("unit" ^^^ Unit) |
      "("~>expression<~")"
  )

}