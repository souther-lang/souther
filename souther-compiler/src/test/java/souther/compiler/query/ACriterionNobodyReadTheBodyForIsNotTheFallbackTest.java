package souther.compiler.query;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A behavior whose meetings nobody read is held to neither criterion, and says so by having none.
 *
 * <p>The choice is the model's: a body whose decisions meet is held to those, and one whose
 * decisions meet nowhere to the combinations of its positions. Both of those are answers about the
 * model, and both need a reading of the body to have been made. A reading that was never made is
 * not a third answer — it is the absence of one — and taking it for "meets nowhere" hands the
 * behavior to the pair space because this compiler did not get far enough, which is the criterion
 * moving with the run.
 *
 * <p>Told apart from a behavior with no body to read. That one has a reading: it finds no meeting,
 * which is why the fallback is what it is held to and why an injected behavior is measured at all.
 */
class ACriterionNobodyReadTheBodyForIsNotTheFallbackTest {

    /** An injected behavior: nothing to read a meeting out of, and the pair space is the answer. */
    private static final String INJECTED = """
            module example.injected

            data A
            data B
            data Flag = A | B
            data Res = { n: Int }

            behavior pick : (x: Flag, y: Flag) -> Res

            example pick
                | "one" : (A, A) -> Res { n = 1 }
            """;

    /** With no reading of the meetings there is no criterion, whatever the positions divide into. */
    @Test
    void aBehaviorWithNoReadingOfItsMeetingsHasNoCriterion() {
        PartitionEvidence partition = partitionOf();

        assertNotNull(partition, "the positions of this behavior were measured");
        assertNull(CombinationCriterion.of(null, partition),
                "a reading nobody made does not say the decisions meet nowhere");
    }

    /** And a behavior with no body has one, which is what keeps the fallback reachable. */
    @Test
    void aBehaviorWithNoBodyIsHeldToThePairSpace() {
        Map<String, InteractionEvidence> read =
                compiled().db().ask(new Adequacy.Interacts("example.injected")).value();

        assertNotNull(read, "a module with no elaborated body is still read for its meetings");
        assertNotNull(read.get("pick"), "and the behavior in it is one of the answers");
        assertInstanceOf(CombinationCriterion.PairFallback.class,
                CombinationCriterion.of(read.get("pick"), partitionOf()),
                "with no meeting to ask about, the combinations of its positions are the criterion");
    }

    private static PartitionEvidence partitionOf() {
        Map<String, PartitionEvidence> coverage =
                compiled().db().ask(new Adequacy.Coverage("example.injected")).value();
        return coverage == null ? null : coverage.get("pick");
    }

    private static Compilation compiled() {
        if (ANSWERED == null) {
            Compilation compilation = Compilation.ofSource(INJECTED, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            ANSWERED = compilation;
        }
        return ANSWERED;
    }

    private static Compilation ANSWERED;
}
