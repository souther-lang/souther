package souther.compiler.query;

import souther.compiler.partition.ObligationIdentity;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two classes no one value holds together are no combination, in the count and in what is owed.
 *
 * <p>A position under one case of a sum and the case of that sum are such a pair: the inner number
 * is there only where the case is, so the class of it and the other case of the sum cannot both
 * hold. That is the model saying so — {@link souther.compiler.inputs.Requirements.Merge.Conflict}
 * is a fact about what a value can be and not a search that came up short — so nothing is owed
 * there and nothing counts it.
 *
 * <p><b>Both surfaces, because they are two readings that have to agree.</b> How many combinations
 * the space holds is the denominator a report prints; which ones are left is what an author is sent
 * after. A denominator over the whole product and a list filtered by what a value can be would ask
 * for a row at a combination the walk that composes one refuses to look for — which is a run that
 * cannot reach the state where nothing is owed.
 *
 * <p>Told apart from a combination every candidate was refused at. That one is ADR-0091's: a value
 * nothing could build proves nothing, the requirement stands, and what is undecided is whether a
 * row can be written. This is the model itself having no such combination.
 */
class ACombinationTheModelCannotHoldIsNoRequirementTest {

    private static final String MODEL = """
            module example.pairs

            data Held = { n: Int }
            data Empty
            data Choice = Empty | Held
            data In = { choice: Choice }
            data Out = Int

            behavior take : (in: In) -> Out
                constructs Out

            let take (in) = match in.choice with
                | Empty -> Out(0)
                | Held as held -> if held.n > 10 then Out(1) else Out(2)

            example take
                | (In { choice = Empty })              -> Out(0)
                | (In { choice = Held { n = 50 } })    -> Out(1)
            """;

    /**
     * The count is over the combinations a value can be in, and the classes of the inner number are
     * in none of the ones under the other case.
     */
    @Test
    void theSpaceHoldsOnlyTheCombinationsAValueCanBeIn() {
        PartitionEvidence.PairSpace pairs = pairsOf();

        assertTrue(pairs.total() > 0, "the two positions make combinations");
        // The one relation this model has, and it is smaller than the product: the number under
        // the case is there only where the case is, so its classes make no combination with the
        // other case. A test over a model whose every pair is compatible would pass whatever this
        // counted.
        assertEquals(2, pairs.total(),
                "two of the four namings are combinations a value can be in");
        for (PartitionEvidence.PairSpace.AxisPair pair : pairs.space()) {
            assertEquals(sizeOf(pair), pair.total(),
                    () -> "the count of " + pair.between() + " is over the combinations a value can"
                            + " be in, and not over the product of the classes");
        }
    }

    /**
     * And what is left to write is counted the same way.
     *
     * <p>The walk that names the combinations no row is in and the count beside it are two readings
     * of one space. What is owed is what the count says is left, and a list longer than that is a
     * list holding something nothing asks for.
     */
    @Test
    void whatIsLeftToWriteIsWhatTheCountSaysIsLeft() {
        PartitionEvidence.PairSpace pairs = pairsOf();
        List<ObligationIdentity.OfAFallbackPairCell> left =
                Coverages.uncovered("take", axesOf(), pairs);

        assertEquals(pairs.unknown(), left.size(),
                () -> "the combinations left over are the ones the count is short of: " + left);
    }

    /** How many combinations of one relation a value can be in, asked of the model. */
    private static long sizeOf(PartitionEvidence.PairSpace.AxisPair pair) {
        List<souther.compiler.partition.Axis> axes = axesOf().axes();
        souther.compiler.partition.Axis one = at(axes, pair.between().one());
        souther.compiler.partition.Axis other = at(axes, pair.between().other());
        long size = 0;
        for (souther.compiler.partition.PartitionClass here : one.classes()) {
            for (souther.compiler.partition.PartitionClass there : other.classes()) {
                if (one.requiring(here).compatibleWith(other.requiring(there))) {
                    size++;
                }
            }
        }
        return size;
    }

    private static souther.compiler.partition.Axis at(
            List<souther.compiler.partition.Axis> axes,
            souther.compiler.partition.AxisId id) {
        return axes.stream().filter(each -> each.id().equals(id)).findFirst()
                .orElseThrow(() -> new AssertionError("no axis " + id));
    }

    private static PartitionEvidence.PairSpace pairsOf() {
        return evidence().pairs();
    }

    private static souther.compiler.partition.MeasuredInput.MeasuredAxes axesOf() {
        return subject().axes();
    }

    private static PartitionEvidence evidence() {
        Map<String, PartitionEvidence> coverage =
                compilation().db().ask(new Adequacy.Coverage("example.pairs")).value();
        PartitionEvidence said = coverage == null ? null : coverage.get("take");
        if (said == null) {
            throw new AssertionError("the behavior was not measured");
        }
        return said;
    }

    private static souther.compiler.partition.MeasuredInput subject() {
        souther.compiler.partition.MeasuredInput said =
                Adequacy.subjectOf(compilation().db(), "example.pairs", "take");
        if (said == null) {
            throw new AssertionError("the behavior has no measured input");
        }
        return said;
    }

    /** One compilation for the whole file: every question here is of the same answers. */
    private static Compilation compilation() {
        if (ANSWERED == null) {
            Compilation compilation = Compilation.ofSource(MODEL, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            ANSWERED = compilation;
        }
        return ANSWERED;
    }

    private static Compilation ANSWERED;
}
