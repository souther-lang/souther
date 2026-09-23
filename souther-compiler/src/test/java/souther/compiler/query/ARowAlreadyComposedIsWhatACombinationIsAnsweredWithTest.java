package souther.compiler.query;

import souther.compiler.partition.ClassDisposition;
import souther.compiler.partition.FillResult;
import souther.compiler.partition.GenerationAnswer;
import souther.compiler.partition.ObligationIdentity;
import souther.compiler.partition.RowId;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A combination a row already composed sits in is answered with that row.
 *
 * <p>One row settles as many requirements as its values settle. The search for a combination of
 * two classes runs after the arms and the classes have had theirs, so by then some of the rows in
 * hand already sit in the combination asked about — and composing another with the same values
 * would hand a person two lines to paste where one does the work, with the second adding nothing a
 * report could point at.
 *
 * <p>Which is a claim about the offer and not about the requirement. The combination is owed either
 * way; what is settled here is where its answer comes from.
 */
class ARowAlreadyComposedIsWhatACombinationIsAnsweredWithTest {

    /** A behavior held to the pair space: two positions it tells apart, meeting nowhere. */
    private static final String MODEL = """
            module example.reuse

            data Domestic
            data Overseas
            data Kind = Domestic | Overseas
            data Amount = Int
                invariant value >= 0
            data Request = { kind: Kind, cost: Amount }
            data Ok = { n: Int }
            data Waiting = { n: Int }

            behavior submit : (request: Request) -> Ok | Waiting
                constructs Ok, Waiting

            let submit (request) = match request.kind with
                | Domestic -> {
                    guard request.cost.value <= 100 else Waiting { n = 1 }
                    Ok { n = 0 }
                }
                | Overseas -> Ok { n = 2 }

            example submit
                | (Request { kind = Domestic, cost = Amount(50) }) -> Ok { n = 0 }
            """;

    /**
     * No combination is answered with a row of values another row of the offer already carries.
     *
     * <p>The reuse itself: where the search finds one in hand it points at it, so a second row of
     * those values is never composed. Held over the values rather than over the count, because two
     * rows differing only in what they were composed for are the two lines a person would be asked
     * to paste.
     */
    @Test
    void aCombinationIsNeverAnsweredWithASecondRowOfValuesTheOfferAlreadyHolds() {
        FillResult filled = fill();

        assertFalse(filled.plan().pairsOwed().isEmpty(), "combinations are owed here");
        Set<RowId> forSomethingElse = composedForSomethingElse(filled);
        Set<Object> theirValues = new LinkedHashSet<>();
        for (RowId each : forSomethingElse) {
            theirValues.add(filled.composed().get(each).inputs());
        }

        List<ObligationIdentity.OfAFallbackPairCell> twice = new ArrayList<>();
        for (GenerationAnswer each : filled.discharge().answers().values()) {
            if (each instanceof GenerationAnswer.Pair(var obligation, var disposition)
                    && disposition instanceof ClassDisposition.Built built
                    && !forSomethingElse.contains(built.rowId())
                    && theirValues.contains(filled.composed().get(built.rowId()).inputs())) {
                twice.add(obligation.target());
            }
        }
        assertEquals(List.of(), twice,
                () -> "each of these was written again with the values a row already had: "
                        + filled.composed().values());
    }

    /** And where one is in hand, that is what the combination's answer points at. */
    @Test
    void aCombinationTheRowsInHandSitInPointsAtOneOfThem() {
        FillResult filled = fill();

        Set<RowId> forSomethingElse = composedForSomethingElse(filled);
        List<ObligationIdentity.OfAFallbackPairCell> reused = new ArrayList<>();
        for (GenerationAnswer each : filled.discharge().answers().values()) {
            if (each instanceof GenerationAnswer.Pair(var obligation, var disposition)
                    && disposition instanceof ClassDisposition.Built built
                    && forSomethingElse.contains(built.rowId())) {
                reused.add(obligation.target());
            }
        }
        assertTrue(!reused.isEmpty(),
                () -> "the rows composed for the arms and the classes sit in some of the"
                        + " combinations: " + filled.discharge().answers().values().stream()
                                .filter(GenerationAnswer.Pair.class::isInstance).toList());
    }

    /** The rows this run composed before any combination was asked about. */
    private static Set<RowId> composedForSomethingElse(FillResult filled) {
        Set<RowId> out = new LinkedHashSet<>();
        for (GenerationAnswer each : filled.discharge().answers().values()) {
            if (each instanceof GenerationAnswer.Class(var _, var disposition)
                    && disposition instanceof ClassDisposition.Built built) {
                out.add(built.rowId());
            }
        }
        for (souther.compiler.partition.ArmDisposition each
                : filled.discharge().arms().values()) {
            if (each instanceof souther.compiler.partition.ArmDisposition.Built built) {
                out.add(built.rowId());
            }
        }
        return out;
    }

    /** What the search made of this behavior, asked of the compilation that made it. */
    private static FillResult fill() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> filled =
                Adequacy.generatedOf(compilation.db(), "example.reuse");
        if (filled == null || filled.get("submit") == null) {
            throw new AssertionError("the behavior was not asked for rows");
        }
        return filled.get("submit").composed();
    }
}
