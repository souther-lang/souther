package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.ElementQuestion;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A binding's elements stand to another's in one way, and which way it is decides nothing on its
 * own.
 *
 * <p>Two things are held here. That there is one way: the values a binding holds are the ones
 * another holds or they were made from them, and both at once is a binding whose elements are two
 * things — a state with no reading, which the table refuses rather than resolving by which of the
 * two was written first.
 *
 * <p>And that the way is not a licence. What a walk may do with an edge depends on what it is
 * asking, and the edge does not come back — so a reader cannot take one and settle that for itself.
 * The pair of a question and an edge is answered in one place, and both of these are asked of it.
 *
 * <p>Held against the table rather than against a model. Every edge is one binding of an expansion
 * said of another the same expansion wrote, and the one place that writes them reads a single
 * operation and asks the library one thing about it — so no source puts two on one binding. What can
 * be asked of the primitive is the law, over bindings made by hand.
 */
class TheElementsOfOneBindingStandOneWayToAnothersTest {

    private static final BindingOwner OWNER = new BindingOwner.OfValue("example.walks", "f");

    private static final BindingId ELEMENTS = new BindingId(OWNER, 0);
    private static final BindingId CONTAINER = new BindingId(OWNER, 1);
    private static final BindingId ANOTHER = new BindingId(OWNER, 2);

    /** The same fact written twice is the same fact. */
    @Test
    void oneEdgeWrittenTwiceIsOneEdge() {
        ElementProvenance.Builder twice = new ElementProvenance.Builder();
        twice.derivesFrom(ELEMENTS, CONTAINER);
        twice.derivesFrom(ELEMENTS, CONTAINER);

        ElementProvenance.Builder once = new ElementProvenance.Builder();
        once.derivesFrom(ELEMENTS, CONTAINER);

        assertEquals(once.built(), twice.built(),
                "writing down what is already written down says nothing new");
    }

    /** An edge with no binding at the far end is not an edge. */
    @Test
    void anEdgeRunsToABinding() {
        assertThrows(NullPointerException.class, () -> new ElementEdge.MadeFrom(null),
                "answered, it would be the answer a binding with no edge gets");
        assertThrows(NullPointerException.class, () -> new ElementEdge.TheSameAs(null),
                "and the same of the other one");
    }

    /** Two ways at once is a binding whose elements are two things, and there is no reading of it. */
    @Test
    void twoWaysOnOneBindingAreRefused() {
        ElementProvenance.Builder made = new ElementProvenance.Builder();
        made.derivesFrom(ELEMENTS, CONTAINER);

        assertThrows(IllegalStateException.class, () -> made.holdsTheSameAs(ELEMENTS, CONTAINER),
                "the values came from there and are not those values, so they are not both");

        ElementProvenance.Builder same = new ElementProvenance.Builder();
        same.holdsTheSameAs(ELEMENTS, CONTAINER);

        assertThrows(IllegalStateException.class, () -> same.derivesFrom(ELEMENTS, CONTAINER),
                "and the other way round: the second is not a refinement of the first");
    }

    /** One way to two containers is the same, whichever way it is. */
    @Test
    void oneWayToTwoContainersIsRefused() {
        ElementProvenance.Builder builder = new ElementProvenance.Builder();
        builder.derivesFrom(ELEMENTS, CONTAINER);

        assertThrows(IllegalStateException.class, () -> builder.derivesFrom(ELEMENTS, ANOTHER),
                "elements are made from one container, and keeping the first would drop the second"
                        + " with nothing saying so");
    }

    /**
     * A walk after the elements themselves goes on through either, and one after where a value
     * stands stops where the values stop being the same ones.
     *
     * <p>Both questions of both edges, which is the whole of what an edge comes to. Asked of one
     * question, the table would answer the same for two edges that are not the same fact.
     */
    @Test
    void whatEachEdgeComesToForEachQuestion() {
        ElementProvenance.Builder builder = new ElementProvenance.Builder();
        builder.holdsTheSameAs(ELEMENTS, CONTAINER);
        builder.derivesFrom(ANOTHER, CONTAINER);
        ElementProvenance provenance = builder.built();

        assertEquals(CONTAINER, provenance.predecessorOf(ELEMENTS, ElementQuestion.NAMED_POSITION),
                "the two hold the same values, so a rule about one is a rule about the other");
        assertEquals(CONTAINER, provenance.predecessorOf(ELEMENTS, ElementQuestion.VALUE_ORIGIN),
                "and they came from there as well");

        assertNull(provenance.predecessorOf(ANOTHER, ElementQuestion.NAMED_POSITION),
                "what is made from a position is not that position");
        assertEquals(CONTAINER, provenance.predecessorOf(ANOTHER, ElementQuestion.VALUE_ORIGIN),
                "and it is where it came from");
    }

    /** A binding nothing was said of is answered for neither question. */
    @Test
    void aBindingNothingWasSaidOfHasNoPredecessor() {
        assertNull(ElementProvenance.NONE.predecessorOf(ELEMENTS, ElementQuestion.NAMED_POSITION));
        assertNull(ElementProvenance.NONE.predecessorOf(ELEMENTS, ElementQuestion.VALUE_ORIGIN));
    }
}
