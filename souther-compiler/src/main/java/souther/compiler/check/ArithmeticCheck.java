package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.diag.msg.ArithmeticMessage;
import souther.compiler.types.Type;

import java.util.List;

/**
 * What arithmetic makes of two operand types: the type the operator answers with, or the rule that
 * refuses them.
 *
 * <p>Arithmetic over a numeric newtype is not one rule but several, and they refuse for different
 * reasons — a product leaves the dimension the operands are in, two unlike newtypes never shared
 * one, a newtype over a newtype has no arithmetic to reach. A refusal that answers only yes or no
 * loses which of these was broken, and the message then has to be written by whatever check the
 * expression falls into next. What that check happens to say — that a newtype is not an arithmetic
 * operand — reads as an argument for deleting the newtype, which is the opposite of what every one
 * of these rules asks for. So the answer carries the rule, and the diagnostic is chosen from it
 * rather than re-derived beside it.
 *
 * <p>The rules are asked in the order they are answerable, so that no rule is reported for a
 * question a nearer one had already settled. An operand whose type states nothing breaks no rule,
 * so it is set aside before any of them is asked. Whether arithmetic can read an operand at all is
 * about that operand alone, so it comes next and is asked of each side. What two newtypes make of each
 * other is settled by the operator without consulting their bases — a product is refused whether or
 * not the bases agree — so it comes next. Only then do the bases have to agree, and only then is a
 * newtype paired with a value of that base. Ordering it any other way lets a scale refuse an
 * addition, which is the fault this whole answer exists to remove.
 */
sealed interface ArithmeticCheck {

    /** The operands combine, and the operator answers with {@code resultType}. */
    record Allowed(Type resultType) implements ArithmeticCheck {}

    /**
     * Arithmetic has nothing of its own left to say, and what remains is one type against another:
     * two plain numbers of unlike bases (Int beside Decimal), or an operand whose type states
     * nothing at all. Both are the plain type check's question, and it answers them as it always
     * has — a found-versus-expected block, or absorbing the operand that states nothing, in which
     * case the expression stands.
     *
     * <p>So this is neither an allowance nor a refusal, and it is deliberately not a
     * {@link Refusal}: a refusal names a rule of arithmetic and carries the sentence for it, and
     * there is no such rule here. Handing the question on is the answer, which is what separates it
     * from falling through to whatever check came next.
     */
    record DeferToPlainTypeCheck(Type left, Type right) implements ArithmeticCheck {}

    /** The operands do not combine, by {@code refusal}. */
    record Refused(Refusal refusal) implements ArithmeticCheck {}

    /** Which operand a refusal is about, and so where it is pointed. */
    enum Side { LEFT, RIGHT, BOTH }

    /**
     * A rule of arithmetic, stated as what refuses these operands. The message and its arguments
     * belong to the rule, so that adding a rule cannot leave the diagnostic behind.
     */
    sealed interface Refusal {
        souther.compiler.diag.msg.Reported said();

        Side side();

        /** The fix, stated beside the rule. A rule that refuses without one leaves the author to
         * guess, and the guess a newtype rule invites is to delete the newtype.
         *
         * <p>A rule that holds for every operator has one fix that has to hold for every operator
         * too: what {@code +} takes beside a newtype is not what {@code *} takes, and a fix written
         * for one of them sends the author from this refusal into the next. Where they differ, the
         * fix says both rather than guessing which operator asked. */
        default souther.compiler.diag.msg.Message hint() {
            return null;
        }
    }

    /** Not a number at all: the rule the newtype rules were carved out of. */
    record OperandNotArithmetic(Type operand, Side side) implements Refusal {
        @Override public souther.compiler.diag.msg.Reported said() {
            return new ArithmeticMessage.AnOperandIsNotANumber(Type.show(operand));
        }
    }

    /** A newtype whose value is not directly Int or Decimal — over another newtype, or over
     * something that was never a number. Arithmetic reaches one wrapping and no further. */
    record NoDirectNumericBase(Type newtype, Type wrapped, Side side) implements Refusal {
        @Override public souther.compiler.diag.msg.Reported said() {
            return new ArithmeticMessage.ANewtypeWithNoDirectNumericBase(
                    Type.show(newtype, wrapped), Type.show(wrapped, newtype));
        }

        @Override public souther.compiler.diag.msg.Message hint() {
            return new ArithmeticMessage.ReachTheBaseWithValue(
                    Type.show(newtype, wrapped), Type.show(wrapped, newtype));
        }
    }

    /** Two unlike newtypes: nothing says a quantity of one is a quantity of the other. */
    record DifferentNewtypes(Type left, Type right) implements Refusal {
        @Override public souther.compiler.diag.msg.Reported said() {
            return new ArithmeticMessage.TwoDifferentNewtypes(Type.show(left, right),
                    Type.show(right, left));
        }

        @Override public souther.compiler.diag.msg.Message hint() {
            return new ArithmeticMessage.ConvertOneToTheOthersNewtype();
        }

        @Override public Side side() {
            return Side.BOTH;
        }
    }

    /** A product of two newtypes is a quantity in neither of them. */
    record ProductChangesDimension(Type left, Type right) implements Refusal {
        @Override public souther.compiler.diag.msg.Reported said() {
            return new ArithmeticMessage.AProductChangesDimension(Type.show(left, right),
                    Type.show(right, left));
        }

        @Override public souther.compiler.diag.msg.Message hint() {
            return new ArithmeticMessage.ComputeOnValueAndBuildTheProduct();
        }

        @Override public Side side() {
            return Side.BOTH;
        }
    }

    /** A quotient of two newtypes is a value in neither of them: a bare ratio where they are the
     * same newtype, a quantity per quantity where they are not, and the language expresses
     * neither. */
    record QuotientChangesDimension(Type left, Type right) implements Refusal {
        @Override public souther.compiler.diag.msg.Reported said() {
            return new ArithmeticMessage.AQuotientChangesDimension(Type.show(left, right),
                    Type.show(right, left));
        }

        @Override public souther.compiler.diag.msg.Message hint() {
            return new ArithmeticMessage.ComputeOnValueAndBuildTheQuotient();
        }

        @Override public Side side() {
            return Side.BOTH;
        }
    }

    /** A value of some other base beside a newtype. Reading its own base is one rule of the
     * newtype, asked by every operator, and not a rule of scaling. */
    record ValueOfAnotherBase(Type newtype, Type base, Type value, Side side) implements Refusal {
        @Override public souther.compiler.diag.msg.Reported said() {
            return new ArithmeticMessage.AValueOfAnotherBase(Type.show(newtype, value),
                    Type.show(base), Type.show(value, newtype));
        }

        @Override public souther.compiler.diag.msg.Message hint() {
            return new ArithmeticMessage.WhatEachOperatorTakesBesideANewtype(
                    Type.show(newtype, value), Type.show(base));
        }
    }

    /** A value of the newtype's own base that was not written out: only a literal is read as the
     * newtype standing beside it. */
    record BareValueIsNotALiteral(Type newtype, Type value, Side side) implements Refusal {
        @Override public souther.compiler.diag.msg.Reported said() {
            return new ArithmeticMessage.OnlyALiteralIsReadAsTheNewtype(
                    Type.show(newtype, value), Type.show(value, newtype));
        }

        @Override public souther.compiler.diag.msg.Message hint() {
            return new ArithmeticMessage.BuildItWhereTheValueComesFrom(
                    Type.show(newtype, value));
        }
    }

    /** A number over a newtype is an inverse, so the dimension changes even though scaling does
     * not. */
    record ReciprocalChangesDimension(Type value, Type newtype) implements Refusal {
        @Override public souther.compiler.diag.msg.Reported said() {
            return new ArithmeticMessage.AReciprocalChangesDimension(
                    Type.show(value, newtype), Type.show(newtype, value));
        }

        @Override public souther.compiler.diag.msg.Message hint() {
            return new ArithmeticMessage.ComputeOnValueAndBuildTheReciprocal();
        }

        @Override public Side side() {
            return Side.BOTH;
        }
    }

    /**
     * What {@code op} makes of the operand types, given whether each operand was written as a
     * literal — the one thing about the expression, rather than its type, that the rules read.
     */
    static ArithmeticCheck of(Ast.BinOp op, Type lt, Type rt,
                              boolean leftIsLiteral, boolean rightIsLiteral, Symbols symbols) {
        // A type that states nothing states nothing about being an operand either — the element of
        // an empty collection that context has not fixed, an `unreachable`, an error already
        // reported. None of these breaks a rule of arithmetic, and BottomInfer is where the
        // property is decided rather than in a list kept here.
        if (BottomInfer.answersNoValue(lt) || BottomInfer.answersNoValue(rt)) {
            return new DeferToPlainTypeCheck(lt, rt);
        }
        Type ln = TypeOps.directNumericNewtypeBase(lt, symbols);
        Type rn = TypeOps.directNumericNewtypeBase(rt, symbols);

        Refusal unreadable = unreadable(lt, ln, Side.LEFT, symbols);
        if (unreadable == null) {
            unreadable = unreadable(rt, rn, Side.RIGHT, symbols);
        }
        if (unreadable != null) {
            return new Refused(unreadable);
        }
        if (ln != null && rn != null) {
            return switch (op) {
                case MUL -> new Refused(new ProductChangesDimension(lt, rt));
                case DIV -> new Refused(new QuotientChangesDimension(lt, rt));
                default -> lt.equals(rt)
                        ? new Allowed(lt)
                        : new Refused(new DifferentNewtypes(lt, rt));
            };
        }
        Type leftBase = ln != null ? ln : lt;
        Type rightBase = rn != null ? rn : rt;
        if (!leftBase.equals(rightBase)) {
            if (ln == null && rn == null) {
                return new DeferToPlainTypeCheck(lt, rt);
            }
            return new Refused(ln != null
                    ? new ValueOfAnotherBase(lt, ln, rt, Side.RIGHT)
                    : new ValueOfAnotherBase(rt, rn, lt, Side.LEFT));
        }
        if (ln == null && rn == null) {
            return new Allowed(lt);
        }
        // Exactly one operand wears a newtype; the other is a value of the base it wraps.
        boolean newtypeOnTheLeft = ln != null;
        Type newtype = newtypeOnTheLeft ? lt : rt;
        Type value = newtypeOnTheLeft ? rt : lt;
        Side valueSide = newtypeOnTheLeft ? Side.RIGHT : Side.LEFT;
        if (op == Ast.BinOp.ADD || op == Ast.BinOp.SUB) {
            boolean valueIsLiteral = newtypeOnTheLeft ? rightIsLiteral : leftIsLiteral;
            return valueIsLiteral
                    ? new Allowed(newtype)
                    : new Refused(new BareValueIsNotALiteral(newtype, value, valueSide));
        }
        if (!newtypeOnTheLeft && op == Ast.BinOp.DIV) {
            return new Refused(new ReciprocalChangesDimension(value, newtype));
        }
        return new Allowed(newtype);
    }

    /** Why arithmetic cannot read this operand at all, or {@code null} where it can. A question
     * about one operand, answered without looking at the one beside it. */
    private static Refusal unreadable(Type t, Type numericBase, Side side, Symbols symbols) {
        if (TypeOps.isSingleValueNewtype(t, symbols)) {
            return numericBase == null
                    ? new NoDirectNumericBase(t, TypeOps.wrapped(t, symbols), side)
                    : null;
        }
        return t == Type.INT || t == Type.DECIMAL ? null : new OperandNotArithmetic(t, side);
    }
}
