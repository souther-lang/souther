package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A closure handed an element of what another operation answered is at a position of the input
 * exactly where the answer holds the input's own elements.
 *
 * <p>{@code List.sort} answers the elements it was given in another order and {@code List.filter}
 * some of them, so an element of either is an element of what went in — and a rule written about it
 * is a rule about that position. What the library says of each is already declared, and this is
 * that statement read the way a walk backwards from a value needs it.
 *
 * <p>As far as, and no further. Where an answer holds what a closure made of an element, what was
 * handed on came from a position and is not one. Followed through anyway, a line would be drawn at a
 * position whose values are not the ones the rule is about — which is worse than drawing none, since
 * an author cannot tell it from a line their model really states.
 */
class AnElementReachedThroughAnOperationIsStillThePositionsTest {

    private static final String MODULE = "example.roster";

    private static final String MODEL = """
            module example.roster

            data Person = { age: Int }
            data Count = Int

            behavior counted : (people: List<Person>) -> Count
                constructs Count
            let counted (people) = Count(List.length(FILTERED))
            """;

    private static List<String> axesOf(String filtered) {
        Compilation compilation =
                Compilation.ofSource(MODEL.replace("FILTERED", filtered), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage(MODULE)).value();
        assertNotNull(coverage, () -> "the model under test compiles: " + filtered);
        return coverage.get("counted").axes().stream()
                .map(PartitionEvidence.AxisCoverage::path).toList();
    }

    /** Straight off the parameter, which is where this started. */
    @Test
    void anElementOfTheParameterIsThatPosition() {
        assertEquals(List.of("people[*].age"),
                axesOf("List.filter(p -> p.age >= 18, people)"));
    }

    /** Through an operation whose answer holds the same values. */
    @Test
    void anElementOfWhatSortAnsweredIsTheSamePosition() {
        assertEquals(List.of("people[*].age"),
                axesOf("List.filter(p -> p.age >= 18, List.reverse(people))"));
    }

    /** And through more than one of them. */
    @Test
    void andThroughMoreThanOne() {
        assertEquals(List.of("people[*].age"),
                axesOf("List.filter(p -> p.age >= 18, List.reverse(List.reverse(people)))"));
    }

    /**
     * And through one the library writes as a body, whose name the tree no longer holds.
     *
     * <p>{@code List.distinct} answers the elements it was given, as {@code List.reverse} does, and
     * the library says so of both. What differs is that one is written as a walk and is spliced into
     * whatever calls it — so by the time this reads the tree there is no operation left to ask
     * about, and what it answered would be at a position nothing could name.
     *
     * <p>Which is why the relation is written where the operation still stands. An expansion knows
     * what it is expanding and which of its arguments held the container, and both ends survive it
     * as bindings; recognising it afterwards would read the shape a splice happens to leave.
     */
    @Test
    void andThroughOneTheLibraryWritesAsABody() {
        assertEquals(List.of("people[*].age"),
                axesOf("List.filter(p -> p.age >= 18, List.distinct(people))"));
    }

    /**
     * But not through one whose answer holds what a closure made.
     *
     * <p>Nothing is claimed. The value the rule is about came from {@code people[*].age} and is not
     * it, and what a rule about a value derived from a position comes to is a question nothing here
     * answers — so no line is drawn, and none is drawn in the wrong place either.
     */
    @Test
    void butNotThroughOneWhoseAnswerHoldsWhatAClosureMade() {
        assertEquals(List.of(),
                axesOf("List.filter(n -> n >= 18, List.map(p -> p.age, people))"));
    }
}
