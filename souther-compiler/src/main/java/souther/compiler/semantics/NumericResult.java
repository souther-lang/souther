package souther.compiler.semantics;

import souther.compiler.types.BinOp;
import souther.compiler.types.Type;

/**
 * What an operation computes, where it answers it, and when it answers nothing.
 *
 * @param at       where in what the operation answers the number stands
 * @param computes which arithmetic it is
 * @param unless   the condition under which the union comes back as a case other than the number's,
 *                 or null for an operation whose result is the number itself
 */
public record NumericResult(Answered at, Arithmetic computes, TheOtherCaseWhen unless) {

    public NumericResult {
        java.util.Objects.requireNonNull(at, "a number is answered somewhere");
        java.util.Objects.requireNonNull(computes, "and is some arithmetic");
    }

    /** Where in what an operation answers its number stands. */
    public sealed interface Answered {

        /** The result itself is the number. */
        record Directly() implements Answered {}

        /**
         * One case of the union carries it, told apart by what that case carries.
         *
         * <p>By the type and not by the name of the case. What a primitive-headed case binds is the
         * primitive itself (spec §primitive-arm), so the type is what the arm's pattern already
         * settled and a name would be a second spelling of it.
         */
        record InTheCaseCarrying(Type carried) implements Answered {}
    }

    /** The condition under which the operation answers a case other than the number's. */
    public record TheOtherCaseWhen(ArgumentRef argument, BinOp op, long than) {

        public TheOtherCaseWhen {
            java.util.Objects.requireNonNull(argument, "this one names an argument");
            java.util.Objects.requireNonNull(op, "and how it stands");
        }
    }
}
