package Assign3.Typer

import Assign3.Syntax.Syntax._
import scala.collection.immutable.ListMap

object Typer {
  // ======================================================================
  // Part 1: Typechecking
  // ======================================================================

  val generator = SymGenerator()
  def freshTyVar(): Type =
    val a = generator.freshVar()
    TyVar(a)


  object SubstType extends Substitutable[Type] {
    // swap y and z in e
    def swap(t: Type, y: Variable, z: Variable): Type = {
      def go(t: Type): Type = t match {
        case TyUnit => TyUnit
        case TyInt => TyInt
        case TyBool => TyBool
        case TyString => TyString
        case TyVar(x) => TyVar(swapVar(x, y, z))
        case TyPair(t1, t2) => TyPair(go(t1), go(t2))
        case TyFun(t1, t2) => TyFun(go(t1), go(t2))
        case TyRef(t1) => TyRef(go(t1))
        case TyRecord(ts) => TyRecord(ts.map((x, ty) => (x, go(ty))))
        case TyForall(x, ty) => TyForall(swapVar(x, y, z), go(ty))
      }
      go(t)
    }

    ////////////////////
    // EXERCISE 1     //
    ////////////////////
    def apply(theta: Subst[Type], t: Type): Type = {
      // BEGIN ANSWER
      t match {
        case TyVar(x: Variable) => {
          if theta.contains(x) then theta(x)
          else TyVar(x)
        }
        case TyUnit => TyUnit
        case TyInt => TyInt
        case TyBool => TyBool
        case TyString => TyString
        case TyPair(t1: Type, t2: Type) => TyPair(apply(theta, t1), apply(theta, t2))
        case TyFun(t1: Type, t2: Type) => TyFun(apply(theta, t1), apply(theta, t2))
        case TyRef(ty: Type) => TyRef(apply(theta, ty))
        case TyRecord(tys: Field[Type]) => {
          var new_tys = ListMap[Label, Type]()
          for ((label, label_type) <- tys) {
            new_tys = new_tys + (label -> apply(theta, label_type))
          }
          TyRecord(new_tys)
        }
        case TyForall(a: Variable, ty: Type) => {
          val b_fresh = generator.genVar(a)
          TyForall(b_fresh, apply(theta, swap(ty, a, b_fresh)))
        }

      }
      // END ANSWER
    }
  }

  import SubstType.{apply, subst, comp, ra2AppAssoc, ra2CompAssoc}

  object AppEnv extends Applicable[Type, Env[Type]] {
    def apply(theta: Subst[Type], ctx: Env[Type]): Env[Type] =
      ctx.map((x: Variable, t: Type) => (x, theta +: t))
  }
  import AppEnv.{apply, ra2AppAssoc}

  ////////////////////
  // EXERCISE 2     //
  ////////////////////

  def unify(t1: Type, t2: Type): Subst[Type] = {

    (t1, t2) match {

      case (t1, t2) if t1 == t2 => iota
      // BEGIN ANSWER
      case (tA: TyVar, t: Type) => {
        if freeVars(t).contains(tA.x) then sys.error("unification variable appears in the other type")
        else Subst(tA.x -> t)
      }
      case (t: Type, tA: TyVar) => {
        if freeVars(t).contains(tA.x) then sys.error("unification variable appears in the other type")
        else Subst(tA.x -> t)
      }
      case (t1: TyPair, t2: TyPair) => {
        val theta: Subst[Type] = unify(t1.ty1, t2.ty1)
        theta *: unify(SubstType.apply(theta, t1.ty2), SubstType.apply(theta, t2.ty2))
      }
      case (t1: TyFun, t2: TyFun) =>  {
        val theta = unify(t1.ty1, t2.ty1)
        theta *: unify(SubstType.apply(theta, t1.ty2), SubstType.apply(theta, t2.ty2))
      }
      case (t1: TyRef, t2: TyRef) => unify(t1.ty, t2.ty)
      case (t1: TyRecord, t2: TyRecord) => {
        var theta = Subst[Type]()
        for ((label, label_type) <- t1.tys) {
          theta = theta *: unify(SubstType.apply(theta, label_type), SubstType.apply(theta, label_type))

        }
        theta
      }

      case _ => sys.error("unable to unify")
      // END ANSWER
    }
  }

  // helper functions for common cases
  // unify a sequence of pairs of types
  def unifyList(ts: List[(Type, Type)]): Subst[Type] = {
    ts.foldLeft(iota)((s: Subst[Type], tt: (Type, Type)) => tt match
      case (t1, t2) => unify(s +: t1, s +: t2) *: s)
    }
  // unify a single equation
  def unify1(p: (Type,Type)) = unifyList(List(p._1 <-> p._2))
  // unify two equations
  def unify2(p1: (Type,Type), p2: (Type,Type)) = unifyList(List(p1,p2))



  // Auxiliary functions
  def makeTyScheme(xs: Set[Variable], ty: Type): Type =
    xs.foldLeft(ty)((cty: Type, v: Variable) => TyForall(v, cty))

  def freeVars(t: Type): Set[Variable] = t match {
    case TyUnit => Set()
    case TyInt => Set()
    case TyBool => Set()
    case TyString => Set()
    case TyVar(x) => Set(x)
    case TyPair(t1, t2) => freeVars(t1) union freeVars(t2)
    case TyFun(t1, t2) => freeVars(t1) union freeVars(t2)
    case TyRef(ty) => freeVars(ty)
    case TyRecord(ts) => ts.foldLeft(Set())((set, lty) =>
      {val (l, ty) = lty; set union freeVars(ty)})
    case TyForall(x, ty) => freeVars(ty) diff Set(x)
  }

  def inst(t: Type): (Type, Subst[Type]) = t match {
    case TyForall(a, ty) =>
      val (nty, s1) = inst(ty)
      val fresh_a = freshTyVar()
      val s2 = Subst(a -> fresh_a)
      (s2 +: nty, s2 *: s1)
    case _ => (t, iota)
  }

  def gen(ctx: Env[Type], ty: Type): Type = {
    val fv_ctx = ctx.foldLeft(Set())(
      (vs: Set[Variable], varty: (Variable, Type)) => varty match
        case (_, ty) => vs union freeVars(ty))
    val fv_ty = freeVars(ty)
    val fv_diff = fv_ty diff fv_ctx
    makeTyScheme(fv_diff, ty)
  }

  def isValue(e: Expr): Boolean = e match {
    case Unit => true
    case Num(_) => true
    case Bool(_) => true
    case Str(_) => true
    case Pair(e1, e2) => isValue(e1) && isValue(e2)
    case Lambda(_, _) => true
    case Rec(_, _, _) => true
    case Record(es) => es.foldLeft(true)((b, lty) =>
      {val (l, ty) = lty; b && isValue(ty)})
    case _ => false
  }

  // auxiliary functions characterising common patterns in tyOf
  def checkTyOf(ctx: Env[Type], e1: Expr, ty:Type): Subst[Type] = {
    val (t1, s1) = tyOf(ctx, e1)
    val s2 = unify1(t1 <-> s1 +: ty)
    s2 *: s1
  }

  def checkTyOf2(ctx: Env[Type], e1: Expr, ty1: Type, e2: Expr, ty2: Type): Subst[Type] = {
    val s1 = checkTyOf(ctx,e1,ty1)
    val s2 = checkTyOf(s1 +: ctx, e2,ty2)
    s2 *: s1
  }

  ////////////////////
  // EXERCISE 3     //
  ////////////////////
  // typing: calculate the return type of e, or throw an error
  def tyOf(ctx: Env[Type], e: Expr): (Type, Subst[Type]) = e match {
    // Value
    case v: Value => sys.error("tyOf: values should not appear at this stage")

    // Arithmetic
    case Unit => (TyUnit, iota)
    case Num(n: Integer) => (TyInt, iota)
    case Plus(e1: Expr, e2: Expr) => (TyInt, checkTyOf2(ctx, e1, TyInt, e2, TyInt))
    case Minus(e1: Expr, e2: Expr) => (TyInt, checkTyOf2(ctx, e1, TyInt, e2, TyInt))
    case Times(e1: Expr, e2: Expr) => (TyInt, checkTyOf2(ctx, e1, TyInt, e2, TyInt))

    // Booleans
    case Bool(b: Boolean) => (TyBool, iota)
    case Eq(e1: Expr, e2: Expr) => {
      val (t, s1) = tyOf(ctx, e1)
      val s2 = checkTyOf(s1 +: ctx, e2, t)
      (TyBool, s2 *: s1)
    }
    case IfThenElse(e: Expr, e1: Expr, e2: Expr) => {
      val s0 = checkTyOf(ctx, e, TyBool)
      val (t1, s1) = tyOf(s0 +: ctx, e1)
      val s2 = checkTyOf((s1 *: s0) +: ctx, e2, t1)
      (s2 +: t1, s2 *: s1 *: s0)
    }

    // Strings
    case Str(s: String) => (TyString, iota)
    case Length(e: Expr) => {
      val s = checkTyOf(ctx, e, TyString)
      (TyInt, s)
    }
    case Index(e1: Expr, e2: Expr) => (TyString, checkTyOf2(ctx, e1, TyString, e2, TyInt))
    case Concat(e1, e2) => (TyString, checkTyOf2(ctx, e1, TyString, e2, TyString))

    // BEGIN ANSWER
    case Var(x: Variable) => inst(TyForall(x, ctx(x)))
    case Let(x: Variable, e1: Expr, e2: Expr) => {
      val (t1, s1) = tyOf(ctx, e1)

      if isValue(e1) then {
        val sigma: Type = gen(s1 +: ctx, t1)
        val (t2, s2) = tyOf(s1 +: (ctx + (x -> sigma)), e2)
        (t2, s2 *: s1)
      } else {
        val (t2, s2) = tyOf(s1 +: (ctx + (x -> t1)), e2)
        (t2, s2 *: s1)
      }
    }

    case Apply(e1: Expr, e2: Expr) => {
      val (t1, s1) = tyOf(ctx, e2)
      val a_fresh = freshTyVar()
      val s2 = checkTyOf(s1 +: ctx, e1, TyFun(t1, a_fresh))
      (s2 +: a_fresh, s2 *: s1)
    }
    case Lambda(x: Variable, e: Expr) => {
      val a_fresh = freshTyVar()
      val (t, s) = tyOf(ctx + (x -> a_fresh), e)
      (TyFun(s +: a_fresh, t), s)
    }
    case Rec(f: Variable, x: Variable, e: Expr) => {
      val a_fresh = freshTyVar()
      val b_fresh = freshTyVar()
      val s = checkTyOf(ctx + (f -> TyFun(a_fresh, b_fresh), x -> a_fresh), e, b_fresh)
      (TyFun(s +: a_fresh, s+: b_fresh), s)
    }
    case Pair(e1: Expr, e2: Expr) => {
      val (t1, s1) = tyOf(ctx, e1)
      val (t2, s2) = tyOf(s1 +: ctx, e2)
      (TyPair(s2 +: t1, t2), s2 *: s1)
    }
    case First(e: Expr) => {
      val a_fresh = freshTyVar()
      val b_fresh = freshTyVar()
      val s = checkTyOf(ctx, e, TyPair(a_fresh, b_fresh))
      (s +: a_fresh, s)
    }
    case Second(e: Expr) => {
      val a_fresh = freshTyVar()
      val b_fresh = freshTyVar()
      val s = checkTyOf(ctx, e, TyPair(a_fresh, b_fresh))
      (s +: b_fresh, s)
    }
    case Ref(e: Expr) => {
      val (t, s) = tyOf(ctx, e)
      (TyRef(t), s)
    }
    case Deref(e: Expr) => {
      val a_fresh = freshTyVar()
      val s = checkTyOf(ctx, e, TyRef(a_fresh))
      (s +: a_fresh, s)
    }
    case Assign(e1: Expr, e2: Expr) => {
      val (t, s1) = tyOf(ctx, e2)
      val s2 = checkTyOf(s1 +: ctx, e1, TyRef(t))
      (TyUnit, s2 *: s1)
    }
    case Record(es: Field[Expr]) => {
      var tys = ListMap[Label, Type]()
      var s = Subst[Type]()
      for ((label, exp) <- es) {
        val (t, sn) = tyOf(s +: ctx, exp)
        tys = tys + (label -> t)
        s = s *: sn
      }
      (s +: TyRecord(tys), s)
    }
    case Proj(e: Expr, l: Label) => {
      tyOf(ctx, e) match {
        case (tyRec: TyRecord, s1: Subst[Type]) => {
          return (tyRec.tys(l), s1)
        }
        case (tyVarA: TyVar, s1: Subst[Type]) => {
          val b_fresh = freshTyVar()
          val s2 = unify(tyVarA, TyRecord(ListMap(l -> b_fresh)))
          (s2 +: b_fresh, s2 *: s1)
        }
        case _ => sys.error("unable to project")
      }
    }

    // Syntatic sugars
    case Sequ(e1: Expr, e2: Expr) => {
      val (t1, s1) = tyOf(ctx, e1)
      val (t2, s2) = tyOf(s1 +: ctx, e2)
      (t2, s2 *: s1)
    }
    case LetFun(f: Variable, x: Variable, e1: Expr, e2: Expr) => {
      val a_fresh = freshTyVar()
      val (t1, s1) = tyOf(ctx + (x -> a_fresh), e1)
      val sigma = gen(s1 +: ctx, TyFun(s1 +: a_fresh, t1))
      val (t2, s2) = tyOf(s1 +: (ctx + (f -> sigma)), e2)
      (t2, s2 *: s1)
    }
    case LetRec(f: Variable, x: Variable, e1: Expr, e2: Expr) => {
      val a_fresh = freshTyVar()
      val b_fresh = freshTyVar()
      val s1 = checkTyOf(ctx + (f -> TyFun(a_fresh, b_fresh), x -> a_fresh), e1, b_fresh)
      val sigma = gen(s1 +: ctx, s1 +: TyFun(a_fresh, b_fresh))
      val (t2, s2) = tyOf(s1 +: (ctx + (f -> sigma)), e2)
      (t2, s2 *: s1)
    }
    case LetPair(x: Variable, y: Variable, e1: Expr, e2: Expr) => {
      val b_fresh = freshTyVar()
      val c_fresh = freshTyVar()
      val s1 = checkTyOf(ctx, e1, TyPair(b_fresh, c_fresh))
      val (t, s2) = tyOf(s1 +: (ctx + (x -> (s1 +: b_fresh), y -> (s1 +: c_fresh))), e2)
      (t, s2 *: s1)
    }
    case LetRecord(xs: Field[Variable], e1: Expr, e2: Expr) => {
      var tys = ListMap[Label, Type]()
      var new_ctx = ctx
      for ((label, label_variable) <- xs) {
        val b_fresh = freshTyVar()
        tys = tys + (label -> b_fresh)
        new_ctx = new_ctx + (label_variable -> b_fresh)
      }
      val s1 = checkTyOf(ctx, e1, TyRecord(tys))
      val (t, s2) = tyOf(s1 +: new_ctx, e2)
      (t, s2 *: s1)
    }
    // END ANSWER
  }
}
