package souther.compiler.observe;

import souther.compiler.types.TypeSymbol;


/**
 * What a text stated of an answer, at the grain it stated it.
 *
 * <p>Two grains. A statement writes a value, or it names the case the answer is and nothing under
 * it — {@code | Approved} says which case and says nothing about what is in it, and that is weaker
 * evidence and still evidence.
 *
 * <p>What it states and nothing more. Whether an answer keeps it is asked of what is bound to the
 * declarations the row was read against ({@code CheckedRow.SelfContained#holds}), and not of this:
 * a comparison reachable from a statement is one a reader can make with declarations of its own,
 * and two readings of one row would then answer differently about one answer — which is the whole
 * of what asking the language rather than the reader means.
 */
public sealed interface Expectation {

    /** The whole value. */
    record TheValue(Asserted value) implements Expectation {

        public TheValue {
            if (value == null) {
                throw new IllegalArgumentException("a stated value is a value");
            }
        }
    }

    /**
     * The case the answer is, and nothing under it.
     *
     * <p>Compared on the case, because there is no value under it to compare: holding a whole value
     * against it would report a difference that was never stated. The case an answer is is the
     * declaration it is of, which is what the reading that produced the answer already settled.
     */
    record TheCase(TypeSymbol name) implements Expectation {

        public TheCase {
            if (name == null) {
                throw new IllegalArgumentException("a stated case is a case");
            }
        }
    }
}
