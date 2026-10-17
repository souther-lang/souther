package souther.compiler.program;

import souther.compiler.types.TypeSymbol;

/**
 * What a row states of the answer, as something an output compiles and holds an answer to where the
 * answer is.
 *
 * <p>The counterpart of a row's inputs. What a row hands over arrives as computations an output builds
 * where the behavior runs, and so does what it states of the answer: an implementation running in a
 * host's own process, with nothing of this compiler beside it, is held to the row there. An output
 * that brings the answer back instead asks {@link CheckedRow.SelfContained#holds}; the two agree,
 * because the value compared is the value this compiler compared, and the comparison is the
 * language's equality.
 *
 * <p>Two arms, because a row states one of two things. Neither carries a comparison of its own: an
 * output holding a way to compare beside this would be a second reading of what a row means.
 */
public sealed interface CheckedAssertion {

    /**
     * The row states a whole value, and an answer keeps it when the two are the same value by the
     * language's equality — the equality an output looks a stand-in's table up with, under which a
     * set is its elements, a map its entries, a decimal the amount it stands for, and a value is of
     * its type before it is anything else.
     *
     * <p>The value is what {@link #computing} answers, built where the answer is: the operand the row
     * writes, as the definition its module holds for it. It is not built at the answer's type. A row
     * may state a value of another type than the behavior answers with, and the type it states is
     * part of what it states; a row stating one no answer can be is refused before it gets here.
     *
     * @param computing what computes the stated value; among its module's helpers, so what its body
     *     can end with is {@link CheckedProgram#abortsAt} of it
     */
    record Value(CheckedHelper computing) implements CheckedAssertion {

        public Value {
            if (computing == null) {
                throw new IllegalArgumentException("a stated value is computed by something");
            }
        }
    }

    /**
     * The row states which case the answer is and nothing under it, and an answer keeps it when it
     * is a value of {@link #expected}. What the case holds is not compared, since nothing about it was
     * stated.
     */
    record Case(TypeSymbol expected) implements CheckedAssertion {

        public Case {
            if (expected == null) {
                throw new IllegalArgumentException("a stated case is a case");
            }
        }
    }
}
