import scala.util.parsing.combinator._
import java.io.FileReader
import sys.process._
import java.io._


object VCGen {

  /* Arithmetic expressions. */
  trait ArithExp

  case class Num(value: Int) extends ArithExp
  case class Var(name: String) extends ArithExp
  case class Read(name: String, ind: ArithExp) extends ArithExp
  case class Add(left: ArithExp, right: ArithExp) extends ArithExp
  case class Sub(left: ArithExp, right: ArithExp) extends ArithExp
  case class Mul(left: ArithExp, right: ArithExp) extends ArithExp
  case class Div(left: ArithExp, right: ArithExp) extends ArithExp
  case class Mod(left: ArithExp, right: ArithExp) extends ArithExp
  case class Parens(a: ArithExp) extends ArithExp
  case class AWrite(name: String, ind: ArithExp, value: ArithExp) extends ArithExp


  /* Comparisons of arithmetic expressions. */
  type Comparison = Product3[ArithExp, String, ArithExp]


  /* Boolean expressions. */
  trait BoolExp

  case class BCmp(cmp: Comparison) extends BoolExp
  case class BNot(b: BoolExp) extends BoolExp
  case class BDisj(left: BoolExp, right: BoolExp) extends BoolExp
  case class BConj(left: BoolExp, right: BoolExp) extends BoolExp
  case class BParens(b: BoolExp) extends BoolExp


  trait Assertion
  type Vars = List[Var]
  case class ForAll(v: Vars, a: Assertion) extends Assertion
  case class Exists(v: Vars, a: Assertion) extends Assertion
  case class ANot(a: Assertion) extends Assertion
  case class ADisj(left: Assertion, right: Assertion) extends Assertion
  case class AConj(left: Assertion, right: Assertion) extends Assertion
  case class ACmp(cmp: Comparison) extends Assertion
  case class AImply(left: Assertion, right: Assertion) extends Assertion
  case class AParens(a: Assertion) extends Assertion
  case object False extends Assertion
  case object True extends Assertion

  /* Statements and blocks. */
  trait Statement
  type Block = List[Statement]

  case class Assign(x: String, value: ArithExp) extends Statement
  case class Write(x: String, ind: ArithExp, value: ArithExp) extends Statement
  case class ParAssign(x1: String, x2: String, value1: ArithExp, value2: ArithExp) extends Statement
  case class If(cond: BoolExp, th: Block, el: Block) extends Statement
  case class While(cond: BoolExp, a: List[Assertion], body: Block) extends Statement

  /* Complete programs. */
  type Program = Product4[String, List[Assertion], List[Assertion], Block]

  /* Guarded Commands */
  trait GuardedCommand

  case class Assume(x: Assertion) extends GuardedCommand
  case class Havoc(x: String) extends GuardedCommand
  case class Choice(left: List[GuardedCommand], right: List[GuardedCommand]) extends GuardedCommand
  case class Assert(x: Assertion) extends GuardedCommand



  object ImpParser extends RegexParsers {
    /* General helpers. */
    def pvar  : Parser[String] = "\\p{Alpha}(\\p{Alnum}|_)*".r

    /* Parsing for ArithExp. */
    def num   : Parser[ArithExp] = "-?\\d+".r ^^ (s => Num(s.toInt))
    def atom  : Parser[ArithExp] =
      "(" ~> aexp <~ ")" |
      pvar ~ ("[" ~> aexp <~ "]") ^^ {case v ~ i => Read(v, i)} |
      num | pvar ^^ { Var(_) } |
      "-" ~> atom ^^ { Sub(Num(0), _) }
    def factor: Parser[ArithExp] =
      atom ~ rep("*" ~ atom | "/" ~ atom | "%" ~ atom) ^^ {
        case left ~ list => (left /: list) {
          case (left, "*" ~ right) => Mul(left, right)
          case (left, "/" ~ right) => Div(left, right)
          case (left, "%" ~ right) => Mod(left, right)
        }
      }
    def term  : Parser[ArithExp] =
      factor ~ rep("+" ~ factor | "-" ~ factor) ^^ {
        case left ~ list => (left /: list) {
          case (left, "+" ~ right) => Add(left, right)
          case (left, "-" ~ right) => Sub(left, right)
        }
      }
    def aexp  : Parser[ArithExp] = term

    /* Parsing for Comparison. */
    def comp  : Parser[Comparison] =
      aexp ~ ("=" | "<=" | ">=" | "<" | ">" | "!=") ~ aexp ^^ {
        case left ~ op ~ right => (left, op, right)
      }

    /* Parsing for BoolExp. */
    def batom : Parser[BoolExp] =
      "(" ~> bexp <~ ")" | comp ^^ { BCmp(_) } | "!" ~> batom ^^ { BNot(_) }
    def bconj : Parser[BoolExp] =
      batom ~ rep("&&" ~> batom) ^^ {
        case left ~ list => (left /: list) { BConj(_, _) }
      }
    def bdisj : Parser[BoolExp] =
      bconj ~ rep("||" ~> bconj) ^^ {
        case left ~ list => (left /: list) { BDisj(_, _) }
      }
    def bexp  : Parser[BoolExp] = bdisj


    /* Parsing for Statement and Block. */
    def block : Parser[Block] = rep(stmt)
    def stmt  : Parser[Statement] =
      pvar ~ ("[" ~> aexp <~ "]") ~ (":=" ~> aexp <~ ";") ^^ {
        case v ~ i ~ e => Write(v, i, e)
      } |
      (pvar <~ ":=") ~ (aexp <~ ";") ^^ {
        case v ~ e => Assign(v, e)
      } |
      (pvar <~ ",") ~ (pvar <~ ":=") ~ (aexp <~ ",") ~ (aexp <~ ";") ^^ {
        case v1 ~ v2 ~ e1 ~ e2 => ParAssign(v1, v2, e1, e2)
      } |
      ("if" ~> bexp <~ "then") ~ (block <~ "else") ~ (block <~ "end") ^^ {
        case c ~ t ~ e => If(c, t, e)
      } |
      ("if" ~> bexp <~ "then") ~ (block <~ "end") ^^ {
        case c ~ t => If(c, t, Nil)
      } |
      ("while" ~> (bexp ~ rep("inv" ~> assn)) <~ "do") ~ (block <~ "end") ^^ {
        case c ~ a ~ b => While(c, a, b)
      } 


    /* Parsing for Pre-, Post- Conditions and Logical Assertions */

    def assn : Parser[Assertion] = 
      aimply | aatom | ("forall" ~> forall) | ("exists" ~> exists)

    def forall : Parser[Assertion] = 
      rep(pvar) ~ ("," ~> assn) ^^ {
        case v ~ a => ForAll(v.map(y => Var(y)), a)
      }
    def exists : Parser[Assertion] =
      rep(pvar) ~ ("," ~> assn) ^^ {
        case v ~ a => Exists(v.map(y => Var(y)), a)
      }    
    def asexp  : Parser[Assertion] = adisj
    def aatom : Parser[Assertion] =
      "(" ~> assn <~ ")" | comp ^^ { ACmp(_) } | "!" ~> aatom ^^ { ANot(_) }
    def aconj : Parser[Assertion] =
      aatom ~ rep("&&" ~> aatom) ^^ {
        case left ~ list => (left /: list) { AConj(_, _) }
      }
    def adisj : Parser[Assertion] =
      aconj ~ rep("||" ~> assn) ^^ {
        case left ~ list => (left /: list) { ADisj(_, _) }
      }
    def aimply : Parser[Assertion] = 
      adisj ~ rep("==>" ~> assn) ^^ {
        case left ~ list => (list :\ left) { (x, y) => AImply(y, x) }
      }


    /* Parsing for Program. */
    def prog   : Parser[Program] =
      ("program" ~> pvar ~ rep("pre" ~> assn) ~ rep("post" ~> assn) <~ "is") ~ (block <~ "end") ^^ {
        case n ~ p ~ q ~ b => (n, p, q, b)
      }

  }
  object WPCom{
    var freshvar : Int = 0
    def getfreshvar() : String = {
      freshvar = freshvar + 1
      return freshvar.toString()
    }
    def getprebpost(pro: Program): List[GuardedCommand] = 
      pro match {
        case (n, p, q, b) => (p :\ List[GuardedCommand]()) {(x, y) => traversepre(x, y)} :::
          (b :\ List[GuardedCommand]()) {(x, y) => traversest(x, y)} :::
          (q :\ List[GuardedCommand]()) {(x, y) => traversepost(x, y)}
        // case (n, p, q, b) => (b :\ List[GuardedCommand]()) {(x, y) => traversest(x, y)}
      }
    def traversest(st: Statement, res: List[GuardedCommand]): List[GuardedCommand] =
      st match {
        case Assign(x, value) => {var temp : String = "tmp" + getfreshvar();Assume(ACmp((Var(temp), "=", Var(x)))) :: (Havoc(x) 
          :: Assume(ACmp((Var(x), "=", arsubst(value, temp, x)))) :: res)}
        case If(cond, th, el) => Choice(Assume(booltoas(cond)) :: 
          ((th :\ List[GuardedCommand]()) {(x, y) => traversest(x, y)}),Assume(booltoas(BNot(cond))) :: 
          ((el :\ List[GuardedCommand]()) {(x, y) => traversest(x, y)})) :: res
        case While(cond, a, body) => 
          ((a :\ List[GuardedCommand]()) {(x, y) => Assert(x) :: y}) ::: 
          ((findmodified(body) :\ List[GuardedCommand]()) {(x, y) => Havoc(x) :: y}) :::
          ((a :\ List[GuardedCommand]()) {(x, y) => Assume(x) :: y}) ::: 
          (Choice(Assume(booltoas(cond)) :: 
                    ((body :\ List[GuardedCommand]()) {(x, y) => traversest(x, y)}) ::: 
                    ((a :\ List[GuardedCommand]()) {(x, y) => Assert(x) :: y}) :::
                    (Assume(False) ::
                    List[GuardedCommand]()),
                  Assume(booltoas(BNot(cond))) ::
                    List[GuardedCommand]()) :: res)
        case Write(x, ind, value) => {var temp : String = "tmp" + getfreshvar();Assume(ACmp((Var(temp), "=", Var(x)))) :: (Havoc(x)
          :: Assume(ACmp((Var(x), "=", AWrite(temp, ind, arsubst(value, temp, x))))) :: res)}
        case ParAssign(x1, x2, value1, value2) => {var temp1 : String = "tmp" + getfreshvar();
        var temp2 : String = "tmp" + getfreshvar();Assume(ACmp((Var(temp1), "=", Var(x1)))) :: (Assume(ACmp((Var(temp2), "=", Var(x2))))
        :: Havoc(x1) :: Havoc(x2) :: Assume(ACmp((Var(x1), "=", arsubst(value1, temp1, x1)))) :: Assume(ACmp((Var(x2), "=", arsubst(value2, temp2, x2)))) :: res)}
      }
    def traversepre(a: Assertion, res: List[GuardedCommand]) : List[GuardedCommand] = 
      Assume(a) :: res
    def traversepost(a: Assertion, res: List[GuardedCommand]) : List[GuardedCommand] =
      Assert(a) :: res
    def findmodified(s: List[Statement]) : List[String] = 
      (s :\ List[String]()) {(a, res) => a match {
        case Assign(x, value) => x :: res
        case Write(x, ind, value) => x :: res
        case If(cond, th, el) => findmodified(th) ::: findmodified(el) ::: res
        case While(cond, a, body) => findmodified(body) ::: res
        case ParAssign(x1, x2, value1, value2) => x1 :: x2 :: res 
      }

      }
    def booltoas(bool: BoolExp): Assertion = 
      bool match {
        case BCmp(cmp) => ACmp(cmp)
        case BNot(b) => ANot(booltoas(b))
        case BDisj(left, right) => ADisj(booltoas(left), booltoas(right))
        case BConj(left, right) => AConj(booltoas(left), booltoas(right))
        case BParens(b) => AParens(booltoas(b))
      }
   
    def arsubst(e: ArithExp, t: String, x: String): ArithExp = 
      e match {
        case Num(value) => Num(value)
        case Var(name) => if (name == x) Var(t) else Var(name)
        case Read(name, ind) => if (name.equals(x)) Read(t, arsubst(ind, t, x)) else Read(name, arsubst(ind, t, x))
        case Add(left, right) => Add(arsubst(left, t, x), arsubst(right, t, x))
        case Sub(left, right) => Sub(arsubst(left, t, x), arsubst(right, t, x))
        case Mul(left, right) => Mul(arsubst(left, t, x), arsubst(right, t, x))
        case Div(left, right) => Div(arsubst(left, t, x), arsubst(right, t, x))
        case Mod(left, right) => Mod(arsubst(left, t, x), arsubst(right, t, x))
        case Parens(a) => Parens(arsubst(a, t, x))
        case AWrite(name, ind, value) => if (name == x) AWrite(t, arsubst(ind, t, x), arsubst(value, t, x))
          else AWrite(name, arsubst(ind, t, x), arsubst(value, t, x))
      }
    def assubst(e: Assertion, t: String, x: String): Assertion =
      e match {
        case ForAll(v, a) => ForAll(v.map{case Var(y) => if (y == x) Var(t) else Var(y)}, assubst(a, t, x))
        case Exists(v, a) =>Exists(v.map{case Var(y) => if (y == x) Var(t) else Var(y)}, assubst(a, t, x))
        case ANot(a) => ANot(assubst(a, t, x))
        case ADisj(left, right) => ADisj(assubst(left, t, x), assubst(right, t, x))
        case AConj(left, right) => AConj(assubst(left, t, x), assubst(right, t, x))
        case ACmp((a, b, c)) => ACmp((arsubst(a, t, x), b, arsubst(c, t, x)))
        case AImply(left, right) => AImply(assubst(left, t, x), assubst(right, t, x))
        case False => False
        case True => True
      }
    def wp(lsgc: List[GuardedCommand], b: Assertion): Assertion = 
      (lsgc :\ b) {(a, res) => a match {
        case Assume(as) => AImply(as, res)
        case Havoc(v) => assubst(res, "tmp" + getfreshvar(), v)
        case Assert(as) => AConj(as, res)
        case Choice(left, right) => AConj(wp(left, res), wp(right, res))
      }
    }
  }
  object Z3Solver{
      var decalredint : Set[String] = Set()
      var declaredarray: Set[String] = Set()
      def getas(as: Assertion) : String =
        as match {
          case AImply(left, right) => "(" + "implies " + getas(left) + " " + getas(right) + ")"
          case ANot(a) => "(" + "not " + getas(a) + ")"
          case ADisj(left, right) => "(" +  "or " + getas(left) + " " + getas(right) + ")"
          case AConj(left, right) => "(" + "and " + getas(left) + " " + getas(right) + ")"
          case ACmp((left, op, right)) => "(" + {if (op == "!=") "not (=" + " " + getar(left) + " " + getar(right) + ")) "else op + " " + getar(left) + " " + getar(right) + ")"} 
          case AParens(a) => "(" + getas(a) + ")"
          case False => "false"
          case True => "true"
          case ForAll(v, a) => "(" + "forall" + " " + "(" + (v.map{case Var(y) => "(" + y + " " + "Int" + ")"}.foldRight("")(_ + _)) + ")" + getas(a) + ")"
          case Exists(v, a) => getas(ANot(ForAll(v, a)))
        }
      def getar(ar: ArithExp) : String = 
        ar match {
          case Num(value) => value.toString()
          case Var(name) => name
          case Read(name, ind) => "(" + "select" + " " + name + " " + getar(ind) + ")"
          case Add(left, right) => "(" + "+" + " " + getar(left) + " " + getar(right) + ")"
          case Sub(left, right) => "(" + "-" + " " + getar(left) + " " + getar(right) + ")"
          case Mul(left, right) => "(" + "*" + " " + getar(left) + " " + getar(right) + ")"
          case Div(left, right) => "(" + "/" + " " + getar(left) + " " + getar(right) + ")"
          case Mod(left, right) => "(" + "mod" + " " + getar(left) + " " + getar(right) + ")"
          case Parens(a) => "(" + getar(a) + ")"
          case AWrite(name, ind, value) => "(" + "store" + " " + name + " " + getar(ind) + " " + getar(value) + ")"
        }
      def getdeclare(ar: ArithExp) : Unit =
        ar match {
          case Var(name) => if (decalredint.contains(name) != true) decalredint += name
          case Read(name, ind) => if (decalredint.contains(name)) {decalredint -= name; declaredarray += name} else {declaredarray += name; getdeclare(ind)}
          case AWrite(name, ind, value) => if (decalredint.contains(name)) {decalredint -= name; declaredarray += name} else {declaredarray += name;getdeclare(ind);getdeclare(value)}
          case Num(value) => ;
          case Add(left, right) => {getdeclare(left);getdeclare(right)}
          case Sub(left, right) => {getdeclare(left);getdeclare(right)}
          case Mul(left, right) => {getdeclare(left);getdeclare(right)}
          case Div(left, right) => {getdeclare(left);getdeclare(right)}
          case Mod(left, right) => {getdeclare(left);getdeclare(right)}
          case Parens(a) => getdeclare(a)
        }
      def getardeclare(as: Assertion) : Unit = 
        as match {
          case AImply(left, right) => {getardeclare(left);getardeclare(right)}
          case ANot(a) => getardeclare(a)
          case ADisj(left, right) => {getardeclare(left);getardeclare(right)}
          case AConj(left, right) => {getardeclare(left);getardeclare(right)}
          case ACmp((left, op, right)) => {getdeclare(left);getdeclare(right)}
          case AParens(a) => getardeclare(a)
          case ForAll(v, a) => {v.foreach{getdeclare(_)};getardeclare(a)}
          case Exists(v, a) => {v.foreach{getdeclare(_)};getardeclare(a)}
          case False => ;
          case True => ;
        }
      def matchtype(as: Assertion) : Unit =
        as match {
          case AImply(left, right) => {matchtype(left); matchtype(right)}
          case ANot(a) => matchtype(a)
          case ADisj(left, right) => {matchtype(left); matchtype(right)}
          case AConj(left, right) => {matchtype(left); matchtype(right)}
          case ACmp((Var(x), op, Var(y))) => if (declaredarray.contains(x) | declaredarray.contains(y)) {decalredint -= x; decalredint -= y; declaredarray += x; declaredarray += y}
          case ACmp((left, op, right)) => ;
          case AParens(a) => matchtype(a)
          case ForAll(v, a) => matchtype(a)
          case Exists(v, a) => matchtype(a)
          case False => ;
          case True => ;
        }
      def printdeclare() : String = {
        var res : String = "";
        decalredint.foreach{res += "(" + "declare-const" + " " + _ + " " + "Int" + ")"};
        declaredarray.foreach{res += "(" + "declare-const" + " " + _ + " " + "(" + "Array" + " " + "Int" + " " + "Int" + "))"};
        return res
      }

  }


  def main(args: Array[String]): Unit = {
    val reader = new FileReader(args(0))
    import ImpParser._;
    // println(parseAll(prog, reader).get)
    // println(parseAll(prog, reader))
    val gc = WPCom.getprebpost(parseAll(prog, reader).get)
    val weakestpre = WPCom.wp(gc, True)
    Z3Solver.getardeclare(weakestpre)
    Z3Solver.matchtype(weakestpre)
    var output = Z3Solver.printdeclare()
    output = output + "(assert (not" + Z3Solver.getas(weakestpre) + "))" + "(check-sat)"
    val file = new File("res.txt")
    val bw = new BufferedWriter(new FileWriter(file))
    bw.write(output)
    bw.close()

    var validity : String = "z3 res.txt" !!;
    validity = validity.replace(" ", "");
    validity = validity.replace("\\n", "");
    if (validity contains "unsat") println("Valid") else println("Invalid")
  }
}
