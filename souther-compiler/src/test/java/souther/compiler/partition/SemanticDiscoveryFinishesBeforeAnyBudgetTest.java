package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Measurement;
import souther.compiler.query.PartitionEvidence;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * What a behavior is measured at is settled by the model, and no budget selects among it.
 *
 * <p>A resource limit may bound work; it may not choose which evidence a measure is made from
 * (see this package's documentation). The two are told apart by when they run. What a position is worth is not known until
 * the body has been read — a position no declaration divides gains its first line from a
 * {@code guard} — so a selection made before that is made where the least is known about what it
 * selects, and it cannot be shown afterwards to have chosen well.
 *
 * <p>This held against sources rather than against a constant. A test naming the number a limit was
 * set at passes again as soon as somebody sets a different number; what these ask is whether the
 * evidence a behavior is measured from is all of what its model states.
 */
class SemanticDiscoveryFinishesBeforeAnyBudgetTest {

    /**
     * Twelve positions the declarations divide, and five the body does.
     *
     * <p>A plain {@code Int} has no classes and no cuts until a comparison draws one, so at the
     * point a structural reading finishes it is a position with nothing to measure. Each of these
     * five becomes a boundary when the body is read.
     */
    private static final String DECLARED_AND_COMPARED = """
            module example.discovery

            data A
            data B
            data Flag = A | B
            data Wide = { f1: Flag, f2: Flag, f3: Flag, f4: Flag, f5: Flag, f6: Flag,
                          f7: Flag, f8: Flag, f9: Flag, f10: Flag, f11: Flag, f12: Flag,
                          n1: Int, n2: Int, n3: Int, n4: Int, n5: Int }
            data Res = { n: Int }

            behavior calc : (c: Wide) -> Res
                constructs Res
            let calc (c) = {
                guard c.n1 > 10 else Res { n = 1 }
                guard c.n2 > 20 else Res { n = 2 }
                guard c.n3 > 30 else Res { n = 3 }
                guard c.n4 > 40 else Res { n = 4 }
                guard c.n5 > 50 else Res { n = 5 }
                Res { n = 0 }
            }

            example calc
                | "one" : (Wide { f1 = A, f2 = A, f3 = A, f4 = A, f5 = A, f6 = A, f7 = A, f8 = A,
                                  f9 = A, f10 = A, f11 = A, f12 = A,
                                  n1 = 100, n2 = 100, n3 = 100, n4 = 100, n5 = 100 })
                        -> Res { n = 0 }
            """;

    /** The same, with one compared position instead of five. Written out rather than derived from
     *  the model above, so that neither says what the other is. */
    private static final String ONE_COMPARED = """
            module example.one

            data A
            data B
            data Flag = A | B
            data Wide = { f1: Flag, f2: Flag, f3: Flag, f4: Flag, f5: Flag, f6: Flag,
                          f7: Flag, f8: Flag, f9: Flag, f10: Flag, f11: Flag, f12: Flag,
                          n1: Int }
            data Res = { n: Int }

            behavior calc : (c: Wide) -> Res
                constructs Res
            let calc (c) = {
                guard c.n1 > 10 else Res { n = 1 }
                Res { n = 0 }
            }

            example calc
                | "one" : (Wide { f1 = A, f2 = A, f3 = A, f4 = A, f5 = A, f6 = A, f7 = A, f8 = A,
                                  f9 = A, f10 = A, f11 = A, f12 = A, n1 = 100 }) -> Res { n = 0 }
            """;

    /**
     * A position the declarations divide and one only the body does are measured alike.
     *
     * <p>The count is the point. Twelve fields carry classes off their type and five carry nothing
     * until the body compares them, and seventeen is what a report shows. A budget of twelve counted
     * where a structural reading ends would have dropped a declared position while letting all five
     * compared ones through free, since none of the five was measurable yet — so the number it names
     * and the number a report shows are different numbers, and the one it bounds is the evidence.
     */
    @Test
    void positionsTheBodyDividesAreMeasuredBesideTheOnesTheDeclarationsDo() {
        PartitionEvidence evidence = evidenceFor(DECLARED_AND_COMPARED);

        assertEquals(17, evidence.axes().size(),
                () -> "twelve declared and five compared, all of them divided: " + paths(evidence));
        assertEquals(5, evidence.boundaries().size(),
                () -> "and every compared one carries a line: " + borders(evidence));
        // Both measures answered everything they answer for. A reading that had left a position out
        // would say so here, and saying nothing is what makes the counts above a measurement.
        assertInstanceOf(Measurement.Complete.class, evidence.partitioned());
        assertInstanceOf(Measurement.Complete.class, evidence.bounded());
    }

    /**
     * And one such position is enough, which is what says the answer above is not about how many.
     *
     * <p>The dependency this fixes: a structural reading produces the position, the body's
     * comparison divides it, and the boundary follows from the second. Held apart from the count so
     * that a reading which stopped producing boundaries at all would fail here rather than pass by
     * having no positions to lose them at.
     */
    @Test
    void aPositionOnlyTheBodyDividesStillCarriesItsLine() {
        PartitionEvidence evidence = evidenceFor(ONE_COMPARED);

        assertEquals(1, evidence.boundaries().size(),
                () -> "the compared position carries a line: " + borders(evidence));
        // The axis the line is on, which the border answers for itself. Read off the assessment's
        // `toString` instead, the test would pass on any rendering that happened to contain the
        // field's name and fail on a rendering that changed nothing about the line.
        assertEquals("calc/c.n1", evidence.boundaries().get(0).axis(),
                () -> "and it is the position the body compared: " + borders(evidence));
        assertInstanceOf(Measurement.Complete.class, evidence.bounded());
    }

    private static java.util.List<String> borders(PartitionEvidence evidence) {
        return evidence.boundaries().stream()
                .map(souther.compiler.query.BorderAssessment::axis).toList();
    }

    private static java.util.List<String> paths(PartitionEvidence evidence) {
        return evidence.axes().stream().map(PartitionEvidence.AxisCoverage::path).toList();
    }

    private static PartitionEvidence evidenceFor(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> partitions = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        return partitions.get("calc");
    }
}
