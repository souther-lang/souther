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
            data Pair = List<String>
                invariant List.length(value) >= 2
            data Capped = { items: List<Item> }
                invariant List.length(items) <= 3
            """;

    private static final String BEHAVIOR = """

            behavior %1$s : (ids: List<String>, xs: List<Item>, k: Int, capped: Capped,
                             pair: Pair, tied: List<Tied>) -> Bool
            let %1$s (ids, xs, k, capped, pair, tied) = %2$s
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
        // The container each is of, the values it is asked of, and whether `k` is read.
        record Held(String name, String type, String values, boolean read) {}
        Map<String, Boolean> expected = new LinkedHashMap<>();
        Map<String, Boolean> actual = new LinkedHashMap<>();
        for (Held each : List.of(
                new Held("capTwo", "CapTwo", "xs.value", true),
                new Held("capOne", "CapOne", "xs.value", false),
                new Held("bools", "List<Bool>", "xs", true),
                new Held("one", "List<One>", "xs", false),
                new Held("codes", "List<Code>", "xs", true))) {
            expected.put(each.name(), each.read());
            actual.put(each.name(), kIsRead("""
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
                    """.formatted(each.name(), each.type(), each.values()), each.name() + "Count"));
        }
        assertEquals(expected, actual);
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

    /** Whether {@code k} of {@code behavior} in {@code model} is read: no value of it is left
     *  not shown to be reached. One model each, since the behaviors of a model share the budget. */
    private static boolean kIsRead(String model, String behavior) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        PartitionEvidence evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value().get(behavior);
        assertNotNull(evidence, behavior);
        return evidence.notRead().stream().noneMatch(left -> left.at().equals("k")
                && left.reason()
                        == UndividedPosition.Reason.RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE);
    }

    /**
     * A container that must hold two elements may hold two the statement fails of, so the values of
     * the elements it keeps are none: the count is shown at none, one and two, and a number that
     * takes those three is read.
     */
    @Test
    void aFilterThatMayKeepNoElementLeavesNoneAValueTheCountIsShownAt() {
        String model = """
                module probe

                data K = Int
                    invariant value >= 0 && value <= 2
                data Item = { id: String, qty: Int }
                data Items = List<Item>
                    invariant List.length(value) >= 2

                behavior keptCount : (xs: Items, k: K) -> Bool
                let keptCount (xs, k) = Set.size(Set.fromList(List.map(p -> p.id,
                        List.filter(p -> p.qty > 3, xs.value)))) == k.value
                """;
        assertEquals(true, kIsRead(model, "keptCount"));
    }

    /**
     * What a container is held to and what the place takes are two ends, and the count is read only
     * where the first is no further than the second: a list of truths held to two holds at most the
     * two values a truth has, and one held to three may hold a count no row shows. (How an end is
     * written as a number is the unit test's: a bound at the greatest whole number is no model's,
     * the rules not leaving a container so many.)
     */
    @Test
    void aCountIsReadOnlyWhereTheContainerHoldsNoMoreThanThePlaceTakes() {
        String model = """
                module probe

                data Held = List<Bool>
                    invariant List.length(value) <= %s

                behavior heldCount : (xs: Held, k: Int) -> Bool
                let heldCount (xs, k) = Set.size(Set.fromList(xs.value)) == k
                """;
        assertEquals(true, kIsRead(model.formatted("2"), "heldCount"));
        assertEquals(false, kIsRead(model.formatted("3"), "heldCount"));
    }

    /**
     * Not shown and not reachable are two answers: where the search stopped at a figure before it
     * had tried every element, the figure is said, whatever the ways it left would have shown.
     */
    @Test
    void aSearchCutShortSaysTheFigureAndIsNoAnswerThatTheCountCannotBeReached() {
        Compilation compilation = Compilation.ofSource("""
                module probe

                data Wide = { id: String, f1: Bool, f2: Bool, f3: Bool, f4: Bool, f5: Bool,
                              f6: Bool, f7: Bool, f8: Bool, f9: Bool }

                behavior wideCount : (xs: List<Wide>, k: Int) -> Bool
                let wideCount (xs, k) = Set.size(Set.fromList(List.map(w -> w.id,
                        List.filter(w -> Bool.not(w.f1) && Bool.not(w.f2) && Bool.not(w.f3)
                                && Bool.not(w.f4) && Bool.not(w.f5) && Bool.not(w.f6)
                                && Bool.not(w.f7) && Bool.not(w.f8) && Bool.not(w.f9), xs)))) == k
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        PartitionEvidence evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value().get("wideCount");
        assertNotNull(evidence);
        assertEquals(List.of(CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.figure()),
                evidence.notRead().stream().filter(left -> left.at().equals("k"))
                        .flatMap(left -> left.figures().stream()).distinct().toList());
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
