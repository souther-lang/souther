package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Incompleteness;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A reason a position could not place a row reaches a measure, and not only a list.
 *
 * <p>{@code whyUnclassified} is gathered over every position the model divides, and the same
 * gathering happens again inside each measure counted at one — the reasons a document prints and the
 * reasons a measure is weaker by are two walks over one set of classifications. The walks are not
 * over the same positions: a position with nothing to measure at it is left out of the second, and a
 * measure that returns before it reads the rows never reaches it either.
 *
 * <p>So a reason could be in the list and in no measure, and the document would print a line about a
 * position while its behavior read {@code complete} — which is issue #996 one size down. Measured
 * across the suite it does not happen: every reason a position gives is carried. This holds that
 * where it can be seen, so a change that stops carrying one fails here rather than in a report
 * somebody reads.
 *
 * <p>What it is not is a claim that the second walk is unnecessary. The two ask different questions
 * — which reasons there are, and which of them bear on this measure — and this says the answers to
 * the first are all reachable through the second.
 */
class EveryReasonAPositionGivesIsCarriedByAMeasureTest {

    /** A guard on a position, and the one row that would say where it stands does not come back. */
    private static final String UNREADABLE = """
            module example.unplaced

            data Draft = { n: Int }
            data Ok = { n: Int }

            behavior go : (request: Draft) -> Ok
                constructs Ok

            let go (request) = {
                guard request.n > 0 else Ok { n = 0 }
                Ok { n = request.n }
            }

            example go
                | (Draft { n = 1 }) -> Ok { n = 1 }
            """;

    /** Every reason any measure of this partition went without, as identities. */
    private static Set<Object> carriedBy(PartitionEvidence partition) {
        Set<Object> out = new LinkedHashSet<>();
        partition.partitioned().weakening().observationCauses()
                .forEach(gap -> out.add(gap.identity()));
        partition.pairs().counted().weakening().observationCauses()
                .forEach(gap -> out.add(gap.identity()));
        for (PartitionEvidence.AxisCoverage axis : partition.axes()) {
            axis.reached().weakening().observationCauses().forEach(gap -> out.add(gap.identity()));
        }
        return out;
    }

    @Test
    void aPositionThatCouldNotPlaceARowSaysSoThroughAMeasure() {
        Compilation compilation = Compilation.ofSource(UNREADABLE, "Main");
        compilation.withJvmExampleDeadlines(DoesNotComeBack.overrunningOn(
                DoesNotComeBack.everythingAboutRowsOf("go")));
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        PartitionEvidence partition = compilation.db()
                .ask(new Adequacy.Coverage("example.unplaced")).value().get("go");

        assertFalse(partition.whyUnclassified().isEmpty(),
                "this model is one where a position could not place its row");

        Set<Object> carried = carriedBy(partition);
        for (Incompleteness gap : partition.whyUnclassified()) {
            assertTrue(carried.contains(gap.identity()),
                    () -> "no measure of this behavior is weaker for " + gap.code() + " at "
                            + gap.subject() + ", so a document printing it says something the"
                            + " measures beside it do not: " + partition.whyUnclassified());
        }
    }
}
