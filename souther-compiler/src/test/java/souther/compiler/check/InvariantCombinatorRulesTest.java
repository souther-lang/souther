package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.Prelude;
import souther.compiler.diag.Located;
import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The invariant check binds a combinator's closure parameter to the container's element type, from a
 * table keyed by the operation's name. A rule in that table can be plainly correct and never run —
 * that is what happened when the check was handed a tree where the operations had already become the
 * folds they are — so the table is held to being reachable here rather than measured later.
 *
 * <p>Two halves. A name must survive to where the check reads it: {@code List.fold} does not, being
 * rewritten to {@code List.foldFrom} first, so no rule may be keyed by it. And each name must have a
 * program that fires its rule — a construction inside the closure that discharges only because the
 * element carries its type's invariant, so removing the rule leaves the element unnamed and the
 * construction reported.
 */
class InvariantCombinatorRulesTest {

    /** A program whose closure builds a value that discharges only if {@code fn}'s rule bound the
     * element. The construction is bound by a {@code let} so the closure still answers what the
     * operation asks of it, whatever that is. */
    private record Fires(String fn, String body) {}

    private static final String PREAMBLE = """
            module demo
            data Money = Decimal
                invariant value >= 0m
            data Positive = Decimal
                invariant value >= 0m
            """;

    private static final List<Fires> FIRES = List.of(
            // `foldFrom` is private, so no program can name it. `List.fold` is the sugar that becomes
            // it before this check reads the tree, which is the only way the rule is ever reached —
            // and therefore the only way to fire it from a program.
            new Fires("List.foldFrom", """
                    behavior f : (xs: List<Money>) -> Int constructs Positive
                    let f (xs) = List.fold((acc, x) -> {
                        let p = Positive(x.value)
                        acc
                    }, 0, xs)
                    """),
            new Fires("List.foldRight", """
                    behavior f : (xs: List<Money>) -> Int constructs Positive
                    let f (xs) = List.foldRight((x, acc) -> {
                        let p = Positive(x.value)
                        acc
                    }, 0, xs)
                    """),
            new Fires("List.map", """
                    behavior f : (xs: List<Money>) -> List<Int> constructs Positive
                    let f (xs) = List.map(x -> {
                        let p = Positive(x.value)
                        0
                    }, xs)
                    """),
            new Fires("List.filter", """
                    behavior f : (xs: List<Money>) -> List<Money> constructs Positive
                    let f (xs) = List.filter(x -> {
                        let p = Positive(x.value)
                        true
                    }, xs)
                    """),
            new Fires("List.all", """
                    behavior f : (xs: List<Money>) -> Bool constructs Positive
                    let f (xs) = List.all(x -> {
                        let p = Positive(x.value)
                        true
                    }, xs)
                    """),
            new Fires("List.any", """
                    behavior f : (xs: List<Money>) -> Bool constructs Positive
                    let f (xs) = List.any(x -> {
                        let p = Positive(x.value)
                        true
                    }, xs)
                    """),
            new Fires("List.find", """
                    behavior f : (xs: List<Money>) -> Money constructs Positive, Money
                    let f (xs) = Option.withDefault(Money(0m), List.find(x -> {
                        let p = Positive(x.value)
                        true
                    }, xs))
                    """),
            new Fires("List.partition", """
                    behavior f : (xs: List<Money>) -> Int constructs Positive
                    let f (xs) = {
                        let (yes, no) = List.partition(x -> {
                            let p = Positive(x.value)
                            true
                        }, xs)
                        List.length(yes)
                    }
                    """),
            new Fires("List.flatMap", """
                    behavior f : (xs: List<Money>) -> List<Int> constructs Positive
                    let f (xs) = List.flatMap(x -> {
                        let p = Positive(x.value)
                        [0]
                    }, xs)
                    """),
            new Fires("List.filterMap", """
                    behavior f : (xs: List<Money>) -> List<Int> constructs Positive
                    let f (xs) = List.filterMap(x -> {
                        let p = Positive(x.value)
                        List.get(0, [0])
                    }, xs)
                    """),
            new Fires("List.sortBy", """
                    behavior f : (xs: List<Money>) -> List<Money> constructs Positive
                    let f (xs) = List.sortBy(x -> {
                        let p = Positive(x.value)
                        x.value
                    }, xs)
                    """),
            new Fires("List.groupBy", """
                    behavior f : (xs: List<Money>) -> Int constructs Positive
                    let f (xs) = Map.size(List.groupBy(x -> {
                        let p = Positive(x.value)
                        x.value
                    }, xs))
                    """),
            new Fires("List.indexBy", """
                    behavior f : (xs: List<Money>) -> Int constructs Positive
                    let f (xs) = Map.size(List.indexBy(x -> {
                        let p = Positive(x.value)
                        x.value
                    }, xs))
                    """),
            new Fires("List.allDistinctBy", """
                    behavior f : (xs: List<Money>) -> Bool constructs Positive
                    let f (xs) = List.allDistinctBy(x -> {
                        let p = Positive(x.value)
                        x.value
                    }, xs)
                    """),
            new Fires("List.mapIndexed", """
                    behavior f : (xs: List<Money>) -> List<Int> constructs Positive
                    let f (xs) = List.mapIndexed((i, x) -> {
                        let p = Positive(x.value)
                        i
                    }, xs)
                    """),
            new Fires("Map.fold", """
                    behavior f : (m: Map<String, Money>) -> Int constructs Positive
                    let f (m) = Map.fold((acc, k, v) -> {
                        let p = Positive(v.value)
                        acc
                    }, 0, m)
                    """),
            new Fires("Map.mapValues", """
                    behavior f : (m: Map<String, Money>) -> Int constructs Positive
                    let f (m) = Map.size(Map.mapValues((k, v) -> {
                        let p = Positive(v.value)
                        0
                    }, m))
                    """),
            new Fires("Map.filterEntries", """
                    behavior f : (m: Map<String, Money>) -> Int constructs Positive
                    let f (m) = Map.size(Map.filterEntries((k, v) -> {
                        let p = Positive(v.value)
                        true
                    }, m))
                    """),
            new Fires("Map.updateIfPresent", """
                    behavior f : (m: Map<String, Money>) -> Int constructs Positive
                    let f (m) = Map.size(Map.updateIfPresent("a", v -> {
                        let p = Positive(v.value)
                        v
                    }, m))
                    """),
            new Fires("Map.updateOrInsert", """
                    behavior f : (m: Map<String, Money>, d: Money) -> Int constructs Positive
                    let f (m, d) = Map.size(Map.updateOrInsert("a", d, v -> {
                        let p = Positive(v.value)
                        v
                    }, m))
                    """),
            new Fires("Set.fold", """
                    behavior f : (s: Set<Money>) -> Int constructs Positive
                    let f (s) = Set.fold((acc, x) -> {
                        let p = Positive(x.value)
                        acc
                    }, 0, s)
                    """),
            new Fires("Set.map", """
                    behavior f : (s: Set<Money>) -> Int constructs Positive
                    let f (s) = Set.size(Set.map(x -> {
                        let p = Positive(x.value)
                        x.value
                    }, s))
                    """),
            new Fires("Set.filter", """
                    behavior f : (s: Set<Money>) -> Int constructs Positive
                    let f (s) = Set.size(Set.filter(x -> {
                        let p = Positive(x.value)
                        true
                    }, s))
                    """),
            new Fires("Set.partition", """
                    behavior f : (s: Set<Money>) -> Int constructs Positive
                    let f (s) = {
                        let (yes, no) = Set.partition(x -> {
                            let p = Positive(x.value)
                            true
                        }, s)
                        Set.size(yes)
                    }
                    """),
            new Fires("Option.map", """
                    data Box = { one: Money? }
                    behavior f : (b: Box) -> Int constructs Positive
                    let f (b) = Option.withDefault(0, Option.map(x -> {
                        let p = Positive(x.value)
                        0
                    }, b.one))
                    """));

    @Test
    void everyRuleIsKeyedByANameTheAnalysisStillSees() {
        for (String fn : DischargeRules.combinatorNames()) {
            assertTrue(Prelude.isLibraryFunction(fn), fn + " is not a standard-library operation");
            assertFalse(Prelude.sugared(fn),
                    fn + " is rewritten to another call before this tree is read, so its rule cannot"
                            + " fire — key the rule by what the rewrite leaves");
        }
    }

    @Test
    void everyRuleHasAProgramThatFiresIt() {
        Set<String> covered = FIRES.stream().map(Fires::fn).collect(Collectors.toCollection(TreeSet::new));
        assertEquals(new TreeSet<>(DischargeRules.combinatorNames()), covered,
                "a rule is registered with no program that fires it, or the other way round");
    }

    @Test
    void theElementCarriesItsInvariantIntoEachClosure() {
        for (Fires f : FIRES) {
            Compiler.Compiled c = Compiler.compileWithWarnings(PREAMBLE + f.body());
            long warnings = c.warnings().stream()
                    .filter(d -> d.severity() == Severity.WARNING).count();
            assertEquals(0, warnings,
                    f.fn() + ": the construction in the closure should discharge from the element's"
                            + " own invariant, and does not — the rule did not bind the element");
        }
    }
}
