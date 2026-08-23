package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A row is built around an element of what a collection's elements hold, as around one of its own.
 *
 * <p>Whether a class is being placed inside a collection was asked of how the two paths are
 * written: the position and every position under it behind a dot. A step inside a sequence follows
 * its container with no dot, so a position one collection further in — {@code rows[*][*]} — matched
 * neither test, and the collection was chosen whole. The class was never placed, and the row offered
 * for it held nothing that is in it.
 *
 * <p>Asked step by step instead. A rendering runs the steps together with whatever each is spelled
 * with, so a test on the text has to name every separator a step can wear and gains a case each time
 * one is added — which is what happened here the day a step that is not a field arrived.
 */
class APositionInsideASequenceInsideOneIsPlacedTooTest {

    private static final String MODULE = "example.rows";

    private static final String MODEL = """
            module example.rows

            data Count = Int

            behavior deep : (rows: List<List<Int>>) -> Count
                constructs Count
            let deep (rows) =
                Count(List.length(
                    List.filter(r -> List.length(List.filter(n -> n >= 5, r)) >= 1, rows)))

            example deep
                | "one under" : ([ [ 1 ] ]) -> Count(0)
            """;

    private static Compilation measured() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    /** The line falls at what the inner lists hold. */
    @Test
    void theLineFallsAtWhatTheInnerListsHold() {
        var coverage = measured().db().ask(new Adequacy.Coverage(MODULE)).value();
        assertNotNull(coverage, "the model under test compiles");

        assertEquals(List.of("rows[*][*]"), coverage.get("deep").axes().stream()
                .map(souther.compiler.query.PartitionEvidence.AxisCoverage::path).toList());
    }

    /**
     * And the row offered for the class it does not cover holds a value that is in it.
     *
     * <p>The whole of it. A row built without placing the class is a collection of collections
     * holding nothing — offered for the class, and in it nowhere.
     */
    @Test
    void theRowOfferedHoldsAValueInTheClass() {
        Map<String, Adequacy.Filling> generated =
                measured().db().ask(new Adequacy.Generated(MODULE)).value();
        assertNotNull(generated, "rows are offered");

        assertEquals(List.of("[[5]]"), generated.get("deep").composed().rows().stream()
                        .map(row -> row.inputs().get(0).text()).toList(),
                () -> "a list holding a list holding a value at or over the line: "
                        + generated.get("deep").composed().reasons());
    }
}
