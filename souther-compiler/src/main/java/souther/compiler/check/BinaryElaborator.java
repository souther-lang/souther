package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticCode;
import souther.compiler.diag.Region;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import java.util.List;
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
                            Diagnostic.of(DiagnosticCode.E1319, "check.compare.ordered")
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
                // The rules live in ArithmeticCheck, which answers with the type the operator gives
                // back or with the rule that refused the operands. Nothing is decided a second time
                // here: a refusal already knows what it is, and this only points it at the source.
                ArithmeticCheck answer = ArithmeticCheck.of(bin.op(), lt, rt,
                        isLiteralExpr(bin.left()), isLiteralExpr(bin.right()), ctx.symbols());
                yield switch (answer) {
                    case ArithmeticCheck.Allowed allowed ->
                            new Core.Binary(bin.op(), left, right, allowed.resultType(), bin.pos());
                    case ArithmeticCheck.DeferToPlainTypeCheck _ -> {
                        // One type against another: the found-versus-expected block says it better
                        // than a sentence would, and requireType raises or absorbs it.
                        Elaborator.requireType(bin.right(), rt, lt, ctx.symbols(), "operand of arithmetic");
                        yield new Core.Binary(bin.op(), left, right, lt, bin.pos());
                    }
                    case ArithmeticCheck.Refused no -> throw refused(bin, no.refusal(), lt, rt);
                };
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
                            Diagnostic.of(DiagnosticCode.E1319, "check.concat.msg")
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
                            Diagnostic.of(DiagnosticCode.E1319, "check.equality.function")
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
                            Diagnostic.of(DiagnosticCode.E1319, "check.compare.msg")
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

    /** The refusal, pointed at the source: at the operand it is about, or — where the rule is about
     * the pair — at the operator with each operand named beside it, as a comparison of two
     * unrelated types is. */
    private static CompileException refused(Ast.Binary bin, ArithmeticCheck.Refusal refusal,
                                            Type lt, Type rt) {
        Diagnostic.Builder d = Diagnostic.of(DiagnosticCode.E1324, refusal.messageKey())
                .args(refusal.messageArgs().toArray());
        if (refusal.hintKey() != null) {
            d = d.hint(refusal.hintKey(), refusal.messageArgs().toArray());
        }
        if (refusal.side() == ArithmeticCheck.Side.BOTH) {
            d = d.at(bin.pos())
                    .secondary(Region.ofWidth(bin.left().pos(), Elaborator.width(bin.left())),
                            "check.operand", Type.show(lt, rt))
                    .secondary(Region.ofWidth(bin.right().pos(), Elaborator.width(bin.right())),
                            "check.operand", Type.show(rt, lt));
        } else {
            Ast.Expr faulted = refusal.side() == ArithmeticCheck.Side.LEFT ? bin.left() : bin.right();
            d = d.at(Region.ofWidth(faulted.pos(), Elaborator.width(faulted)));
        }
        return CompileException.of(d.build(),
                "operand of arithmetic: " + Type.show(lt, rt) + " and " + Type.show(rt, lt));
    }

    /**
     * What {@code op} asks of one operand, given that the operand beside it is {@code other}.
     * {@code onTheRight} says which side the asked-about operand stands on, because the rule is not
     * symmetric.
     *
     * <p>The question a reader of an operand asks — what does standing here make me? — is the same
     * question {@link #elaborateBinary} asks, so it is put to the same rules rather than answered
     * again beside them: each type an operand could be is offered to {@link ArithmeticCheck}, and
     * the one the operator accepts is the answer. Where it accepts neither, nothing follows and the
     * answer is null.
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
        for (Type candidate : List.of(other, base)) {
            Type lt = onTheRight ? other : candidate;
            Type rt = onTheRight ? candidate : other;
            if (ArithmeticCheck.of(op, lt, rt, false, false, symbols) instanceof ArithmeticCheck.Allowed) {
                return candidate;
            }
        }
        return null;
    }

    /** One side is a single-value newtype and the other is a bare literal (not itself a newtype). */
    static boolean literalPairsNewtype(Type lt, Type rt, Ast.Expr le, Ast.Expr re,
                                               Symbols symbols) {
        return (TypeOps.isSingleValueNewtype(lt, symbols) && !TypeOps.isSingleValueNewtype(rt, symbols) && isLiteralExpr(re))
                || (TypeOps.isSingleValueNewtype(rt, symbols) && !TypeOps.isSingleValueNewtype(lt, symbols) && isLiteralExpr(le));
    }
}
