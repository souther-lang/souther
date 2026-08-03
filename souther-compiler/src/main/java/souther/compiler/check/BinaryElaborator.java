package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Region;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import java.util.Map;
import java.util.Set;

/**
 * Typing a binary operator, including the rules that let a single-value newtype compare with and
 * add to a bare literal of its base without losing its own identity (ADR-0047).
 */
public final class BinaryElaborator {

    private BinaryElaborator() {}

    /** Whether either side of {@code bin} has a type the compiler could not work out. */
    private static boolean erroneousOperand(Ast.Binary bin, Scope env,
                                            CheckContext ctx) {
        return erroneous(bin.left(), env, ctx) || erroneous(bin.right(), env, ctx);
    }

    private static boolean erroneous(Ast.Expr operand, Scope env, CheckContext ctx) {
        try {
            return Elaborator.elaborate(operand, env, ctx).type() instanceof Type.Erroneous;
        } catch (CompileException _) {
            return false;   // it has its own error; the operator's check will raise it as before
        }
    }

    static Core elaborateBinary(Ast.Binary bin, Scope env, CheckContext ctx) {
        // An operator wants a particular shape of type — Int or Decimal to add, two lists or two
        // strings to append — and an operand the compiler could not work out has no shape. Absorbing
        // is for a comparison, which can answer "no disagreement"; there is no answer to give here, so
        // the definition is abandoned and the name that denoted nothing stands as what was wrong.
        // Left alone, the operand's type reaches the message as `?`, which names nothing the author
        // could go looking for.
        if (erroneousOperand(bin, env, ctx)) {
            throw new Unanswerable(bin.pos());
        }
        return switch (bin.op()) {
            case AND, OR -> {
                Core left = Elaborator.requireTyped(bin.left(), Type.BOOL, env, ctx,
                        "operand of logical operator");
                Core right = Elaborator.requireTyped(bin.right(), Type.BOOL, env, ctx,
                        "operand of logical operator");
                yield new Core.Binary(bin.op(), left, right, Type.BOOL, bin.pos());
            }
            case LT, LE, GT, GE -> {
                // The ordered primitives: Int numerically, String lexicographically, Decimal by
                // value, Date/DateTime in time. Unlike Elm (which orders only Int/Float/Char/String
                // because it rides JavaScript), Souther sits on the JVM where BigDecimal/LocalDate/
                // LocalDateTime are Comparable, so it orders them too. A single-value newtype over an
                // ordered type is ordered by that value; the operands stay the same newtype (nominal),
                // except that a bare literal takes the other side's newtype from context.
                Core left = Elaborator.elaborate(bin.left(), env, ctx);
                Core right = Elaborator.elaborate(bin.right(), env, ctx);
                Type lt = left.type();
                Type rt = right.type();
                if (!orderedComparable(lt, rt, bin.left(), bin.right(), ctx.symbols())) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.compare.ordered").title("check.type.mismatch.title")
                                    .at(bin.pos()).args(Type.show(lt), Type.show(rt)).build(),
                            "operand of comparison must be two ordered values of the same type (Int,"
                                    + " String, Decimal, Date, DateTime, a newtype over one of these, or"
                                    + " one enumeration), got " + lt + " and " + rt);
                }
                yield new Core.Binary(bin.op(), left, right, Type.BOOL, bin.pos());
            }
            case ADD, SUB, MUL, DIV -> {
                // `+ - * /` work on two Int or two Decimal operands (spec 18.1). Int aborts on
                // overflow and `/` aborts on a zero divisor; Decimal `/` rounds by the default
                // scale/mode. Case handling for a zero divisor is the `divide`/`remainder` functions.
                Core left = Elaborator.elaborate(bin.left(), env, ctx);
                Core right = Elaborator.elaborate(bin.right(), env, ctx);
                Type lt = left.type();
                Type rt = right.type();
                boolean addSub = bin.op() == Ast.BinOp.ADD || bin.op() == Ast.BinOp.SUB;
                // Closed newtype arithmetic (spec §newtype-arithmetic): `+`/`-` over a single-value
                // numeric newtype yield that newtype. The result is re-wrapped and its invariant re-checked at construction,
                // which a behavior's guard discharges. The operands are the same newtype, or a newtype
                // with a bare literal of its base (as for comparison).
                if (addSub && arithClosedNewtype(lt, rt, bin.left(), bin.right(), ctx.symbols())) {
                    Type result = TypeOps.closedNewtypeArithResult(lt, rt, ctx.symbols());
                    yield new Core.Binary(bin.op(), left, right, result, bin.pos());
                }
                // Scalar newtype arithmetic: `*`/`/` scale a numeric newtype by a plain Int/Decimal of
                // the same base (`金額 * 2`), staying in the newtype — the dimension is unchanged.
                // `金額 * 金額` and `金額 * 数量` (a dimension change / units, not modeled) fall through
                // to the base path below, an error.
                if (!addSub && scalarNewtypeArith(lt, rt, bin.op(), ctx.symbols())) {
                    Type result = TypeOps.closedNewtypeArithResult(lt, rt, ctx.symbols());
                    yield new Core.Binary(bin.op(), left, right, result, bin.pos());
                }
                if (lt != Type.INT && lt != Type.DECIMAL) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.arith.operand").title("check.type.mismatch.title")
                                    .at(bin.pos()).args(Type.show(lt)).build(),
                            "operand of arithmetic must be Int or Decimal, got " + lt);
                }
                Elaborator.requireType(bin.right(), rt, lt, ctx.symbols(), "operand of arithmetic");   // rt reused, no re-type
                yield new Core.Binary(bin.op(), left, right, lt, bin.pos());
            }
            case CONCAT -> {
                // `++` is Elm's appendable operator: two strings concatenate to a string, two lists to
                // a list (spec 18.1). Strings are checked first, before the empty-list absorption below.
                Core left = Elaborator.elaborate(bin.left(), env, ctx);
                Core right = Elaborator.elaborate(bin.right(), env, ctx);
                Type lraw = left.type();
                Type rraw = right.type();
                if (lraw == Type.STRING && rraw == Type.STRING) {
                    yield new Core.Binary(bin.op(), left, right, Type.STRING, bin.pos());
                }
                // A bottom operand ({@code Nothing}) is a list read from an accumulator an empty
                // collection seed grows — the value at a key of a `Map.empty`-seeded fold, whose element
                // type is not fixed yet. At run time it is a list, so read it as the empty list and let
                // the other operand fix the element type, as `[] ++ xs` does.
                Type lt = BottomInfer.bottomAsEmptyList(lraw);
                Type rt = BottomInfer.bottomAsEmptyList(rraw);
                if (!(lt instanceof Type.ListOf lo) || !(rt instanceof Type.ListOf ro)) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.concat.msg")
                                    .title("check.concat.title")
                                    .at(bin.pos(), 2)
                                    .secondary(Region.ofWidth(bin.left().pos(), Elaborator.width(bin.left())),
                                            "check.operand", Type.show(lt, rt))
                                    .secondary(Region.ofWidth(bin.right().pos(), Elaborator.width(bin.right())),
                                            "check.operand", Type.show(rt, lt))
                                    .args(Type.show(lt, rt), Type.show(rt, lt))
                                    .build(),
                            "`++` needs two lists or two strings, got " + lt + " and " + rt);
                }
                yield new Core.Binary(bin.op(), left, right,
                        Type.list(BottomInfer.unifyElem(lo.element(), ro.element(), bin.pos())), bin.pos());
            }
            case EQ, NE -> {
                Core left = Elaborator.elaborate(bin.left(), env, ctx);
                Core right = Elaborator.elaborate(bin.right(), env, ctx);
                Type lt = left.type();
                Type rt = right.type();
                // two values of the same data compare by their fields (spec 16.2); across different
                // types there is nothing to compare. An operand may be the scalar empty-collection
                // bottom (`Nothing`) when it reads an accumulator a `[]` seed grows — the `e` in
                // `if any(e -> e == x, acc) …` over a `fold(…, [], xs)` is bound to the not-yet-fixed
                // element type (ADR-0028). At run time it holds the other operand's type, so absorb the
                // bottom rather than reject the comparison. (A whole empty list `[]` stays a type error
                // against a non-list, so this does not loosen `[] == 5`.)
                // A sum may also be compared with one of its cases (`役職 == 一般社員`): a case value
                // is a value of its sum (case->sum is transparent everywhere else, spec §sum-data), so
                // this is a sum-vs-sum comparison by case (spec §equality). Check the relation on the
                // top-level case sets directly, not through `assignable` — `assignable` recurses into
                // collections (covariance), which would wrongly let `List<一般社員> == List<役職>` compare;
                // the exemption is only the direct sum<->case scalar relationship. Unrelated types
                // (`金額 == 数量`) have disjoint case sets and still fail.
                // `==` is value equality, and a function value has none: comparing two would fall
                // back to whether they are the same object, which is not a question the language asks
                if (!TypeOps.supportsEquality(lt, ctx.symbols())
                        || !TypeOps.supportsEquality(rt, ctx.symbols())) {
                    Type carrier = TypeOps.supportsEquality(lt, ctx.symbols()) ? rt : lt;
                    throw CompileException.of(
                            Diagnostic.of(null, "check.equality.function")
                                    .title("check.compare.title")
                                    .at(bin.pos(), 2).args(Type.show(carrier)).build(),
                            "a function has no value to compare, so " + Type.show(carrier)
                                    + " cannot be an operand of `==` or `/=`");
                }
                Set<TypeName> lCases = TypeOps.leafCases(lt, ctx.symbols());
                Set<TypeName> rCases = TypeOps.leafCases(rt, ctx.symbols());
                boolean caseOfSum = !lCases.isEmpty() && !rCases.isEmpty()
                        && (lCases.containsAll(rCases) || rCases.containsAll(lCases));
                if (!lt.equals(rt) && !eqCoercible(lt, rt, bin.left(), bin.right(), ctx.symbols())
                        && !caseOfSum && !BottomInfer.isBottom(lt) && !BottomInfer.isBottom(rt)) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.compare.msg")
                                    .title("check.compare.title")
                                    .at(bin.pos(), 2)
                                    .secondary(Region.ofWidth(bin.left().pos(), Elaborator.width(bin.left())),
                                            "check.operand", Type.show(lt, rt))
                                    .secondary(Region.ofWidth(bin.right().pos(), Elaborator.width(bin.right())),
                                            "check.operand", Type.show(rt, lt))
                                    .args(Type.show(lt, rt), Type.show(rt, lt))
                                    .build(),
                            "cannot compare " + lt + " with " + rt);
                }
                yield new Core.Binary(bin.op(), left, right, Type.BOOL, bin.pos());
            }
        };
    }

    /** A source literal (Int/Decimal/String/Bool, or a negated literal) — the only thing allowed to
     * take a newtype from the other operand. A variable of the underlying type is not (write the
     * newtype construction, e.g. {@code 金額(x)}). */
    static boolean isLiteralExpr(Ast.Expr e) {
        return e instanceof Ast.IntLit || e instanceof Ast.DecimalLit
                || e instanceof Ast.StringLit || e instanceof Ast.BoolLit
                || (e instanceof Ast.Neg n && isLiteralExpr(n.operand()));
    }

    /** Whether {@code <}/{@code <=}/{@code >}/{@code >=} may compare the operands: both must reduce to
     * the same ordered base, and be either the same nominal type or a newtype paired with a bare
     * literal of its base (so {@code 金額 <= 金額} and {@code 金額 <= 100} pass, {@code 金額 <= 数量}
     * and {@code 金額 <= (Int variable)} do not). */
    static boolean orderedComparable(Type lt, Type rt, Ast.Expr le, Ast.Expr re,
                                             Symbols symbols) {
        Type lb = TypeOps.base(lt, symbols);
        if (!TypeOps.isOrdered(lb) || !lb.equals(TypeOps.base(rt, symbols))) {
            // An enumeration is ordered by its declaration, and a case value is a value of its sum
            // (spec 8.3), so `stage < Won` compares in the sum both sides belong to (issue #161).
            return TypeOps.comparisonEnumeration(lt, rt, symbols) != null;
        }
        if (lt.equals(rt)) {
            return true;
        }
        return literalPairsNewtype(lt, rt, le, re, symbols);
    }

    /** Whether {@code ==}/{@code /=} may pair a newtype with a bare literal of its base type (the
     * same-type and bottom cases are handled by the caller). */
    static boolean eqCoercible(Type lt, Type rt, Ast.Expr le, Ast.Expr re,
                                       Symbols symbols) {
        return TypeOps.base(lt, symbols).equals(TypeOps.base(rt, symbols))
                && literalPairsNewtype(lt, rt, le, re, symbols);
    }

    /** Whether {@code +}/{@code -} may combine the operands as closed newtype arithmetic: a
     * single-value newtype whose value is Int or Decimal, paired with the same newtype, or with a
     * bare literal of that base. A nested newtype (value is another newtype) and {@code *}/{@code /}
     * are excluded; {@code 金額 - 数量} (two different newtypes) is not combinable and falls through
     * to the base-only path (an error). This is the one home of the admissibility rule; codegen and
     * the invariant analysis run on validated code and only pick the result via
     * {@link TypeOps#closedNewtypeArithResult}. */
    static boolean arithClosedNewtype(Type lt, Type rt, Ast.Expr le, Ast.Expr re,
                                              Symbols symbols) {
        Type ln = TypeOps.directNumericNewtypeBase(lt, symbols);
        Type rn = TypeOps.directNumericNewtypeBase(rt, symbols);
        if (ln == null && rn == null) {
            return false;   // no newtype operand — the plain Int/Decimal path handles it
        }
        if (lt.equals(rt)) {
            return ln != null;   // same single-value newtype over a numeric base
        }
        if (ln != null && !TypeOps.isSingleValueNewtype(rt, symbols) && isLiteralExpr(re) && rt.equals(ln)) {
            return true;        // 金額 + 100 (the literal takes 金額)
        }
        return rn != null && !TypeOps.isSingleValueNewtype(lt, symbols) && isLiteralExpr(le) && lt.equals(rn);
    }

    /** Whether {@code *}/{@code /} scales a single-value numeric newtype by a plain Int/Decimal of the
     * same base (`金額 * 2`, `2 * 金額`, `金額 / 2`), staying in the newtype. One operand is such a
     * newtype and the other is the bare base (Int/Decimal, literal or variable — a scalar is not
     * coerced to the newtype, it stays a plain number). {@code newtype × newtype} (a dimension change /
     * units, not modeled — spec §newtype-arithmetic) is excluded. Division is not commutative: only
     * {@code newtype / scalar} scales; {@code scalar / newtype} (`2 / 金額`) is an inverse — a
     * dimension change — so a scalar on the left is admitted for {@code *} only. */
    static boolean scalarNewtypeArith(Type lt, Type rt, Ast.BinOp op, Symbols symbols) {
        Type ln = TypeOps.directNumericNewtypeBase(lt, symbols);
        Type rn = TypeOps.directNumericNewtypeBase(rt, symbols);
        if (ln != null && rn == null && rt.equals(ln)) {
            return true;   // 金額 * 2, 金額 / 2 — newtype on the left, scalar on the right
        }
        // scalar on the left (2 * 金額) is fine only for `*`; 2 / 金額 is an inverse, rejected.
        return op == Ast.BinOp.MUL && rn != null && ln == null && lt.equals(rn);
    }

    /**
     * What {@code op} asks of one operand, given that the operand beside it is {@code other}.
     * {@code onTheRight} says which side the asked-about operand stands on, because the rule is not
     * symmetric.
     *
     * <p>Arithmetic and comparison relate two values of one type, so mostly the answer is {@code other}
     * itself. Scaling a numeric newtype is where they differ: {@code N * s}, {@code s * N} and
     * {@code N / s} stay in {@code N}, so the operand beside a numeric newtype is the bare base it
     * wraps, and {@code N × N} is a dimension change the model does not have. Where the operator admits
     * neither — {@code s / N} is an inverse — nothing follows and the answer is null.
     *
     * <p>This is the rule {@link #elaborateBinary} checks, answered for the question a reader of an
     * operand asks: what does standing here make me? Both are stated here so that neither can be
     * changed without the other in view.
     */
    static Type operandBeside(Ast.BinOp op, Type other, boolean onTheRight, Symbols symbols) {
        if (op == Ast.BinOp.AND || op == Ast.BinOp.OR) {
            return Type.BOOL;
        }
        if (other == null) {
            return null;
        }
        Type base = TypeOps.directNumericNewtypeBase(other, symbols);
        if (base == null || !(op == Ast.BinOp.MUL || op == Ast.BinOp.DIV)) {
            return other;
        }
        Type lt = onTheRight ? other : base;
        Type rt = onTheRight ? base : other;
        return scalarNewtypeArith(lt, rt, op, symbols) ? base : null;
    }

    /** One side is a single-value newtype and the other is a bare literal (not itself a newtype). */
    static boolean literalPairsNewtype(Type lt, Type rt, Ast.Expr le, Ast.Expr re,
                                               Symbols symbols) {
        return (TypeOps.isSingleValueNewtype(lt, symbols) && !TypeOps.isSingleValueNewtype(rt, symbols) && isLiteralExpr(re))
                || (TypeOps.isSingleValueNewtype(rt, symbols) && !TypeOps.isSingleValueNewtype(lt, symbols) && isLiteralExpr(le));
    }
}
