package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * How many different values a container holds, held against another number, is shown to reach
 * every value the other number stands at where the container may hold that many different values:
 * a row of j elements that differ at the place the values are taken from is a row of the count at
 * j, and a count of the values of the elements a statement keeps is shown at j by j elements that
 * differ there and meet the statement.
 *
 * <p>A count is shown only as far as the container reaches. A type with few values, a rule that
 * ties the values to what the statement reads, a cap on how many the container holds, and a
 * statement no element meets each leave the number beside the count not shown at the values past
 * what the count reaches.
 *
 * <p>The numbers the statement reads are the statement's own comparison's, and the count leaves
 * none of them unread.
 */
class ACountOfDifferentValuesReachesWhatItIsHeldAgainstTest {

    private static final String DECLARATIONS = """
            module probe

            data Item = { id: String, qty: Int, flag: Bool }
            data Tied = { id: String, qty: Int }
                invariant qty <= 3 || id == "fixed"
            data Code = String
                invariant String.matches("[A-Z]{3}", value)
            data One = String
                invariant value == "x"
            data Pair = List<String>
                invariant List.length(value) >= 2
            data Capped = { items: List<Item> }
                invariant List.length(items) <= 3
            """;

    private static final String BEHAVIOR = """

            behavior %1$s : (ids: List<String>, xs: List<Item>, k: Int, flags: List<Bool>,
                             capped: Capped, codes: List<Code>, ones: List<One>, pair: Pair,
                             tied: List<Tied>) -> Bool
            let %1$s (ids, xs, k, flags, capped, codes, ones, pair, tied) = %2$s
            """;

    /** A count and the number it is held against, and whether that number is read. */
    private record Case(String body, String against, boolean read) {

        /** The count and the place that is asked about it: one count is asked of more than one. */
        String label() {
            return against + " of " + body;
        }
    }

    private static final List<Case> CASES = cases();

    private static List<Case> cases() {
        String byId = "Set.size(Set.fromList(List.map(p -> p.id, xs)))";
        String keptIds = "Set.size(Set.fromList(List.map(p -> p.id,"
                + " List.filter(p -> p.qty > 3, xs))))";
        return List.of(
                // The values of the elements themselves, of a field of each, and of the elements a
                // filter keeps.
                new Case("Set.size(Set.fromList(ids)) == k", "k", true),
                new Case(byId + " == k", "k", true),
                new Case(keptIds + " == k", "k", true),
                // The places the statement reads are the statement's own comparison's.
                new Case(keptIds + " == k", "xs[*].qty", true),
                // A type with two values has no more than two different ones, a name that wraps
                // a pattern as many as the pattern has, and a name that wraps one value one.
                new Case("Set.size(Set.fromList(flags)) == k", "k", false),
                new Case("Set.size(Set.fromList(codes)) == k", "k", false),
                new Case("Set.size(Set.fromList(List.map(o -> o.value, ones))) == k", "k", false),
                // A container that must hold two elements holds a value, and so one different
                // value at least: the count is none of the numbers below one.
                new Case("Set.size(Set.fromList(pair.value)) == k", "k", true),
                // A cap on how many the container holds is a cap on the count.
                new Case("Set.size(Set.fromList(List.map(p -> p.id, capped.items))) == k", "k",
                        false),
                // A rule that ties the value to what the statement reads leaves a value the
                // statement keeps no value of its own: here only one.
                new Case("Set.size(Set.fromList(List.map(p -> p.id,"
                        + " List.filter(p -> p.qty > 3, tied)))) == k", "k", false),
                // A statement no element meets keeps no value.
                new Case("Set.size(Set.fromList(List.map(p -> p.id,"
                        + " List.filter(p -> p.flag && Bool.not(p.flag), xs)))) == k", "k",
                        false),
                // A statement over the value itself keeps the values it holds of, which are not
                // the values the type has.
                new Case("Set.size(Set.fromList(List.filter(s -> s == \"a\", ids))) == k", "k",
                        false));
    }

    private static Map<String, PartitionEvidence> measured() {
        StringBuilder source = new StringBuilder(DECLARATIONS);
        int at = 0;
        for (Case each : CASES) {
            source.append(BEHAVIOR.formatted("case" + at++, each.body()));
        }
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return compilation.db().ask(new Adequacy.Coverage("probe")).value();
    }

    private static final Map<String, PartitionEvidence> MEASURED = measured();

    /**
     * Held against a number that takes none, one and two, a count is read where the container
     * reaches two different values and not where it reaches fewer: the cap on how many it holds,
     * the values its type has.
     */
    @Test
    void aCountIsReadAgainstANumberOnlyWhereTheContainerReachesEveryValueOfIt() {
        Map<String, Boolean> read = new LinkedHashMap<>();
        read.put("capTwo", true);
        read.put("capOne", false);
        read.put("bools", true);
        read.put("one", false);
        read.put("codes", true);
        Map<String, String> held = new LinkedHashMap<>();
        held.put("capTwo", "CapTwo, xs.value");
        held.put("capOne", "CapOne, xs.value");
        held.put("bools", "List<Bool>, xs");
        held.put("one", "List<One>, xs");
        held.put("codes", "List<Code>, xs");
        Map<String, Boolean> actual = new LinkedHashMap<>();
        for (String name : read.keySet()) {
            String[] type = held.get(name).split(", ");
            // One model for each: the behaviors of a model share what the measure may spend.
            Compilation compilation = Compilation.ofSource("""
                    module probe

                    data K = Int
                        invariant value >= 0 && value <= 2
                    data One = String
                        invariant value == "x"
                    data Code = String
                        invariant String.matches("[A-Z]{3}", value)
                    data CapTwo = List<String>
                        invariant List.length(value) <= 2
                    data CapOne = List<String>
                        invariant List.length(value) <= 1

                    behavior %1$sCount : (xs: %2$s, k: K) -> Bool
                    let %1$sCount (xs, k) = Set.size(Set.fromList(%3$s)) == k.value
                    """.formatted(name, type[0], type[1]), "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            assertEquals(List.of(), compilation.errors().stream()
                    .map(each -> each.diagnostic().code()).toList(),
                    "the model under test compiles");
            PartitionEvidence evidence =
                    compilation.db().ask(new Adequacy.Coverage("probe")).value().get(name + "Count");
            assertNotNull(evidence, name);
            actual.put(name, evidence.notRead().stream().noneMatch(left ->
                    left.at().equals("k") && left.reason() == UndividedPosition.Reason
                            .RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE));
        }
        assertEquals(read, actual);
    }

    /**
     * Two elements the statement keeps that hold different values are found, and a rule that
     * leaves the kept elements short ids shows no more than that: the strings the type of the place
     * has are not the values an element the statement keeps may hold, so the count is not shown at
     * every value up to how many elements the container holds.
     */
    @Test
    void aRuleThatTiesTheValuesToWhatTheStatementReadsLeavesTheCountUnread() {
        Compilation compilation = Compilation.ofSource("""
                module probe

                data Short = { id: String, qty: Int }
                    invariant qty <= 3 || String.length(id) <= 2

                behavior shortCount : (xs: List<Short>, k: Int) -> Bool
                let shortCount (xs, k) = Set.size(Set.fromList(List.map(p -> p.id,
                        List.filter(p -> p.qty > 3, xs)))) == k
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        PartitionEvidence evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value().get("shortCount");
        assertNotNull(evidence);
        assertEquals(true, evidence.notRead().stream().anyMatch(left -> left.at().equals("k")
                && left.reason()
                        == UndividedPosition.Reason.RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE));
    }

    @Test
    void aCountOfDifferentValuesIsShownToReachWhatItIsHeldAgainstAsFarAsTheContainerReaches() {
        Map<String, Boolean> refused = new LinkedHashMap<>();
        int at = 0;
        for (Case each : CASES) {
            PartitionEvidence evidence = MEASURED.get("case" + at++);
            assertNotNull(evidence, each.body());
            refused.put(each.label(), evidence.notRead().stream().anyMatch(left ->
                    left.at().equals(each.against())
                            && left.reason() == UndividedPosition.Reason
                                    .RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE));
        }
        Map<String, Boolean> expected = new LinkedHashMap<>();
        CASES.forEach(each -> expected.put(each.label(), !each.read()));
        assertEquals(expected, refused);
    }
}
