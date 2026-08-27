package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A position the item fixes and the way narrows is decided once.
 *
 * <p>They are one statement said two ways. The item asks for a place of the position's order; the
 * way says the value there turned out to be a case of it — and a row writes one value at one
 * location, so it is built under the narrowing and accepted at the place. Handed over as both a
 * fixed value and a requirement, it is a position with two accounts, which {@link ConstructionPlan}
 * refuses with a sentence about callers.
 *
 * <p><b>An ordinary model reaches it.</b> An enumeration is compared on the order its cases are
 * declared in, so a comparison written inside an arm of a match on that same value draws its line on
 * the position the arm narrows. Nothing about that is a corner: the two vocabularies simply meet,
 * which is what the way was carried to the composer for.
 */
class OnePositionIsDecidedOnceWhereTheItemAndTheWayBothReachItTest {

    /**
     * A line on an enumeration, drawn inside an arm of a match on the same position.
     *
     * <p>{@code stage < Won} is over {@code stage}'s order; the arm says {@code stage} is a
     * {@code Prospecting}. Both are about the one parameter.
     */
    private static final String STAGE = """
            module example.stage

            data Stage = Prospecting | Won

            behavior f : (stage: Stage) -> Bool

            let f (stage) =
                match stage with
                    | Prospecting -> stage < Won
                    | Won         -> false
            """;

    /**
     * The model is answered rather than refused, and the point the arm admits is offered its row.
     *
     * <p>The row is the case the arm selects, because that is the value the narrowing builds and the
     * place accepts. What the point at the other case gets is the second half of this and is below.
     */
    @Test
    void theRowIsBuiltUnderTheNarrowingAndAcceptedAtThePlace() {
        assertEquals(List.of("Prospecting"), rowsOffered(),
                "a row for the point the arm admits, composed as the case the arm selects");
    }

    /**
     * And the point the arm refuses is offered none.
     *
     * <p>No row reaching that comparison has {@code stage} at the other case, so there is nothing to
     * offer. Said as a row that was not seen reaching it rather than as a proof: what settles it is
     * the walk that reads a row at a point, and that walk reports what it saw.
     */
    @Test
    void thePointTheArmRefusesIsOfferedNothing() {
        assertEquals(List.of("stage = Won"), whatWasNotResolved(),
                "the point at the case the arm is not in");
    }

    private static List<String> rowsOffered() {
        return boundaries().rows().stream()
                .flatMap(row -> row.inputs().stream())
                .map(FixtureTemplate::text)
                .toList();
    }

    private static List<String> whatWasNotResolved() {
        return boundaries().unresolved().stream()
                .flatMap(each -> each.classes().stream())
                .toList();
    }

    private static Generator.GenerationResult boundaries() {
        Compilation compilation = Compilation.ofSource(STAGE, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> filled =
                Adequacy.generatedOf(compilation.db(), "example.stage");
        assertNotNull(filled, "the model under test compiles and is answered about");
        return filled.get("f").boundaries();
    }
}
