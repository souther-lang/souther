package souther.compiler;

import souther.compiler.partition.GenerationOutcome;
import souther.compiler.partition.Generator;
import souther.compiler.partition.ObligationIdentity;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Offering;
import souther.compiler.query.OfferingRequest;
import souther.compiler.query.PartitionEvidence;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An element whose case a closure matches is a position the body tells apart, so its cases are
 * paired with the other positions — and with a count of the container only where the count leaves
 * the container something to hold.
 *
 * <p>Which case went which way is not read: the closure is applied to every element, a different
 * case each time. So no class of the element is said to take one way, and a row is still owed for
 * each case beside each class of the count that can hold it.
 *
 * <p>And a row for such a pair holds the element. A class of the count taking none and some, beside
 * a case of an element, is a list of one, which the class takes — never the empty list its values
 * may have been written at.
 */
class AnElementsCaseMatchedInAClosureIsPairedWithTheListsLengthTest {

    private static final String MODULE = "example.regions";

    private static final String MODEL = """
            module example.regions

            import List ( all, length )

            data North
            data South
            data Region = North | South

            data Usage = { regions: List<Region> }
            data Out = Int

            behavior northern : (u: Usage) -> Out
                constructs Out

            let northern (u) = {
                guard length(u.regions) >= %d else Out(0)
                guard all(r -> match r with
                    | North -> true
                    | South -> false, u.regions) else Out(1)
                Out(2)
            }

            example northern
                | (Usage { regions = [] }) -> Out(0)
            """;

    /**
     * The list with an element meets both cases of what it holds, and the empty list neither.
     */
    @Test
    void theCasesOfTheElementArePairedWithTheCountThatHoldsOne() {
        PartitionEvidence northern = measured(MODEL.formatted(1), MODULE, "northern");

        assertEquals(2, sizeOf(northern, "List.length(u.regions)", "u.regions[*]"),
                () -> "a list of one or more meets both cases and an empty list neither: "
                        + northern.pairs().space());
    }

    /** A map's keys likewise, beside how many the map holds. */
    @Test
    void theCasesOfAKeyArePairedWithTheSizeThatHoldsOne() {
        PartitionEvidence counted = measured("""
                module example.keys

                data North
                data South
                data Region = North | South

                data Usage = { counts: Map<Region, Int> }
                data Out = Int

                behavior northern : (u: Usage) -> Out
                    constructs Out

                let northern (u) = {
                    guard Map.size(u.counts) >= 1 else Out(0)
                    guard List.all(k -> match k with
                        | North -> true
                        | South -> false, Map.keys(u.counts)) else Out(1)
                    Out(2)
                }

                example northern
                    | (Usage { counts = [] }) -> Out(0)
                """, "example.keys", "northern");

        assertEquals(2, sizeOf(counted, "Map.size(u.counts)", "u.counts[key]"),
                () -> "a map of one or more meets both cases of its key and an empty map neither: "
                        + counted.pairs().space());
    }

    /**
     * A count of fewer than two beside a case of the element: one element, of that case.
     */
    @Test
    void aCountTakingNoneAndSomeHoldsTheElementOfTheCaseAsked() {
        List<Adequacy.GenerationDisposition> said = generated(MODEL.formatted(2));

        for (String region : List.of("North", "South")) {
            List<String> rows = rowsFor(said,
                    Set.of("List.length(u.regions)/0 <= x < 2", region));
            assertTrue(!rows.isEmpty() && rows.stream().allMatch(row ->
                            row.equals("Usage { regions = [" + region + "] }")),
                    () -> "one " + region + " beside a list of fewer than two: " + rows + " of "
                            + said);
        }
    }

    private static long sizeOf(PartitionEvidence evidence, String one, String other) {
        for (PartitionEvidence.PairSpace.AxisPair pair : evidence.pairs().space()) {
            String a = pair.between().one().term();
            String b = pair.between().other().term();
            if ((a.equals(one) && b.equals(other)) || (a.equals(other) && b.equals(one))) {
                return pair.total();
            }
        }
        throw new AssertionError("no pair of " + one + " and " + other + ": "
                + evidence.pairs().space());
    }

    private static PartitionEvidence measured(String model, String module, String behavior) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage(module)).value();
        PartitionEvidence said = coverage == null ? null : coverage.get(behavior);
        assertNotNull(said, () -> behavior + " was not measured: " + compilation.diagnostics());
        return said;
    }

    /** The first input of every row offered for the obligation naming exactly {@code classes}. */
    private static List<String> rowsFor(List<Adequacy.GenerationDisposition> said,
                                        Set<String> classes) {
        for (Adequacy.GenerationDisposition each : said) {
            if (each.item().isPresent() && classIdsOf(each.item().get()).equals(classes)) {
                if (!(each.outcome() instanceof GenerationOutcome.Generated generated)) {
                    return List.of();
                }
                List<String> out = new ArrayList<>();
                for (Generator.GeneratedRow row : generated.candidates()) {
                    out.add(row.inputs().getFirst().text());
                }
                return out;
            }
        }
        throw new AssertionError("nothing is owed at " + classes + ": " + said);
    }

    private static Set<String> classIdsOf(ObligationIdentity item) {
        return switch (item) {
            case ObligationIdentity.OfAClass one -> Set.of(one.classOfAPosition().classId());
            case ObligationIdentity.OfAFallbackPairCell pair -> {
                Set<String> ids = new LinkedHashSet<>();
                pair.classes().forEach(each -> ids.add(each.classId()));
                yield ids;
            }
            default -> Set.of();
        };
    }

    private static List<Adequacy.GenerationDisposition> generated(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Offering offering = Adequacy.offeredFor(compilation.db(),
                OfferingRequest.overTheModule(MODULE));
        List<Adequacy.GenerationDisposition> out = new ArrayList<>();
        offering.searched().values().forEach(filling -> out.addAll(filling.generation()));
        return out;
    }
}
