package souther.compiler.check;

import souther.compiler.types.BindingId;

import java.util.Objects;

/**
 * How the elements of what one binding holds stand to the elements of another's.
 *
 * <p>One edge per binding and not a table per kind. Where an operation answers the elements it was
 * given the two bindings hold the same values, and where it answers what a closure made of them the
 * values came from there and are not those values; a binding cannot be both, since what wrote the
 * edge read one operation and the library says one thing about it. Held as two tables, that was a
 * fact about the writer rather than about the value, and a reader met it as an order to try them in.
 *
 * <p><b>Not handed out.</b> What an edge licenses depends on what a walk is asking
 * ({@link souther.compiler.inputs.ElementQuestion}), and a reader that could hold one would be free
 * to answer that for itself — which is the same defect as reading the two tables in an order of its
 * own, one step further in. So this is read where it is interpreted
 * ({@link ElementProvenance#stepFrom}) and nowhere else.
 */
sealed interface ElementEdge {

    /** The binding at the other end. */
    BindingId container();

    /**
     * The two bindings hold the same values, so a rule about one is a rule about the other.
     *
     * <p>An edge with no binding at the far end is refused here rather than where one is written.
     * What such a value would come to is a walk answered "nothing to go on to", which is what a
     * binding with no edge at all comes to — so the two would be one answer, and an edge that lost
     * its end would read as a binding nothing was said of.
     */
    record TheSameAs(BindingId container) implements ElementEdge {

        public TheSameAs {
            Objects.requireNonNull(container, "an edge runs to a binding");
        }
    }

    /** The elements were made from the other binding's, so they came from there and are not
     *  those values. Likewise no edge without a binding at the far end. */
    record MadeFrom(BindingId container) implements ElementEdge {

        public MadeFrom {
            Objects.requireNonNull(container, "an edge runs to a binding");
        }
    }
}
