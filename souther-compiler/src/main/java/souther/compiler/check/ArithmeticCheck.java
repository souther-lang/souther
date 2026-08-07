package souther.compiler.check;

import souther.compiler.ast.Ast;
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
 * <p>The refusals group semantically: operands that do not agree ({@link DifferentNewtypes},
 * {@link BareValueIsNotALiteral}, {@link ScalarOfAnotherBase}), a result whose dimension the
 * language cannot express ({@link ProductChangesDimension}, {@link QuotientChangesDimension},
 * {@link ReciprocalChangesDimension}), and a representation arithmetic does not reach
 * ({@link NoDirectNumericBase}). The grouping is not itself a type: nothing switches on it, and a
 * layer of interfaces no code reads would only be another place to keep in step.
 */
sealed interface ArithmeticCheck {

    /** The operands combine, and the operator answers with {@code resultType}. */
    record Allowed(Type resultType) implements ArithmeticCheck {}

    /** The operands do not combine, by {@code refusal}. */
    record Refused(Refusal refusal) implements ArithmeticCheck {}

    /** Which operand a refusal is about, and so where it is pointed. */
    enum Side { LEFT, RIGHT, BOTH }

    /**
     * A rule of arithmetic, stated as what refuses these operands. The message and its arguments
     * belong to the rule, so that adding a rule cannot leave the diagnostic behind.
     */
    sealed interface Refusal {
        String messageKey();

        List<Object> messageArgs();

        Side side();

        /** The fix, stated beside the rule. A rule that refuses without one leaves the author to
         * guess, and the guess a newtype rule invites is to delete the newtype. */
        default String hintKey() {
            return messageKey() + ".hint";
        }
    }

    /** Not a number at all: the rule the newtype rules were carved out of. */
    record OperandNotArithmetic(Type operand) implements Refusal {
        @Override public String messageKey() {
            return "check.arith.operand";
        }

        @Override public List<Object> messageArgs() {
            return List.of(Type.show(operand));
        }

        @Override public Side side() {
            return Side.LEFT;
        }

        @Override public String hintKey() {
            return null;   // Int or Decimal is the whole of it; there is nothing else to say
        }
    }

    /**
     * Int against Decimal. The found-versus-expected block the plain type check already renders says
     * this better than a sentence would, so this refusal names no message of its own and the caller
     * asks that check to speak.
     */
    record PrimitiveBasesDisagree(Type left, Type right) implements Refusal {
        @Override public String messageKey() {
            throw new UnsupportedOperationException("rendered by the plain type check");
        }

        @Override public List<Object> messageArgs() {
            return List.of();
        }

        @Override public Side side() {
            return Side.RIGHT;
        }

        @Override public String hintKey() {
            return null;
        }
    }

    /** Two unlike newtypes: nothing says a quantity of one is a quantity of the other. */
    record DifferentNewtypes(Type left, Type right) implements Refusal {
        @Override public String messageKey() {
            return "check.arith.newtype.incompatible";
        }

        @Override public List<Object> messageArgs() {
            return List.of(Type.show(left), Type.show(right));
        }

        @Override public Side side() {
            return Side.BOTH;
        }
    }

    /** A bare value of the base that is not a literal: only a literal is read as the newtype. */
    record BareValueIsNotALiteral(Type newtype, Type bare, Side side) implements Refusal {
        @Override public String messageKey() {
            return "check.arith.newtype.scalar";
        }

        @Override public List<Object> messageArgs() {
            return List.of(Type.show(newtype), Type.show(bare));
        }
    }

    /** A scalar of some other base: scaling reads the newtype's own base and no other. */
    record ScalarOfAnotherBase(Type newtype, Type base, Type bare, Side side) implements Refusal {
        @Override public String messageKey() {
            return "check.arith.newtype.scalarbase";
        }

        @Override public List<Object> messageArgs() {
            return List.of(Type.show(newtype), Type.show(base), Type.show(bare));
        }
    }

    /** A product of two newtypes is a quantity in neither of them. */
    record ProductChangesDimension(Type left, Type right) implements Refusal {
        @Override public String messageKey() {
            return "check.arith.newtype.product";
        }

        @Override public List<Object> messageArgs() {
            return List.of(Type.show(left), Type.show(right));
        }

        @Override public Side side() {
            return Side.BOTH;
        }
    }

    /** A quotient of two newtypes is a bare ratio, which is again neither of them. */
    record QuotientChangesDimension(Type left, Type right) implements Refusal {
        @Override public String messageKey() {
            return "check.arith.newtype.quotient";
        }

        @Override public List<Object> messageArgs() {
            return List.of(Type.show(left), Type.show(right));
        }

        @Override public Side side() {
            return Side.BOTH;
        }
    }

    /** A scalar over a newtype is an inverse, so the dimension changes even though scaling does not. */
    record ReciprocalChangesDimension(Type scalar, Type newtype) implements Refusal {
        @Override public String messageKey() {
            return "check.arith.newtype.reciprocal";
        }

        @Override public List<Object> messageArgs() {
            return List.of(Type.show(scalar), Type.show(newtype));
        }

        @Override public Side side() {
            return Side.BOTH;
        }
    }

    /** A newtype whose value is not directly Int or Decimal — over another newtype, or over
     * something that was never a number. Arithmetic reaches one wrapping and no further. */
    record NoDirectNumericBase(Type newtype, Type wrapped, Side side) implements Refusal {
        @Override public String messageKey() {
            return "check.arith.newtype.nested";
        }

        @Override public List<Object> messageArgs() {
            return List.of(Type.show(newtype), Type.show(wrapped));
        }
    }

    /**
     * What {@code op} makes of the operand types, given whether each operand was written as a
     * literal — the one thing about the expression, rather than its type, that the rules read.
     */
    static ArithmeticCheck of(Ast.BinOp op, Type lt, Type rt,
                              boolean leftIsLiteral, boolean rightIsLiteral, Symbols symbols) {
        boolean addSub = op == Ast.BinOp.ADD || op == Ast.BinOp.SUB;
        Type ln = TypeOps.directNumericNewtypeBase(lt, symbols);
        Type rn = TypeOps.directNumericNewtypeBase(rt, symbols);
        boolean leftIsNewtype = TypeOps.isSingleValueNewtype(lt, symbols);
        boolean rightIsNewtype = TypeOps.isSingleValueNewtype(rt, symbols);

        if (!leftIsNewtype && !rightIsNewtype) {
            if (lt != Type.INT && lt != Type.DECIMAL) {
                return new Refused(new OperandNotArithmetic(lt));
            }
            if (!lt.equals(rt)) {
                return new Refused(new PrimitiveBasesDisagree(lt, rt));
            }
            return new Allowed(lt);
        }
        if (leftIsNewtype && ln == null) {
            return new Refused(new NoDirectNumericBase(lt, TypeOps.wrapped(lt, symbols), Side.LEFT));
        }
        if (rightIsNewtype && rn == null) {
            return new Refused(new NoDirectNumericBase(rt, TypeOps.wrapped(rt, symbols), Side.RIGHT));
        }
        if (ln != null && rn != null) {
            if (addSub) {
                return lt.equals(rt) ? new Allowed(lt) : new Refused(new DifferentNewtypes(lt, rt));
            }
            return new Refused(op == Ast.BinOp.MUL
                    ? new ProductChangesDimension(lt, rt)
                    : new QuotientChangesDimension(lt, rt));
        }
        // Exactly one operand is a numeric newtype; the other is a bare value standing beside it.
        boolean newtypeOnTheLeft = ln != null;
        Type newtype = newtypeOnTheLeft ? lt : rt;
        Type base = newtypeOnTheLeft ? ln : rn;
        Type bare = newtypeOnTheLeft ? rt : lt;
        Side bareSide = newtypeOnTheLeft ? Side.RIGHT : Side.LEFT;
        if (!bare.equals(base)) {
            return new Refused(new ScalarOfAnotherBase(newtype, base, bare, bareSide));
        }
        if (addSub) {
            boolean bareIsLiteral = newtypeOnTheLeft ? rightIsLiteral : leftIsLiteral;
            return bareIsLiteral
                    ? new Allowed(newtype)
                    : new Refused(new BareValueIsNotALiteral(newtype, bare, bareSide));
        }
        if (!newtypeOnTheLeft && op == Ast.BinOp.DIV) {
            return new Refused(new ReciprocalChangesDimension(bare, newtype));
        }
        return new Allowed(newtype);
    }
}
