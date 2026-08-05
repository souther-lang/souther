package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A rule saying what a construction keeps of the container it was built from is worth having only
 * where something can travel through it. What the check states of a container it names by that
 * container's kind, so a rule between kinds carries nothing however true it is — which is why the
 * operations that answer the same elements in another kind of container are among the ones there is
 * nothing to say of rather than rules.
 *
 * <p>So every rule is held here to a program that discharges only because of it: a size the
 * construction keeps, or an upper bound on the size where it can only drop. Removing the rule leaves
 * the clause reported. The set is the table's own, not a list written beside it — a rule added with
 * no program that fires it fails this, which is what happened to the whole table when nothing held
 * it: dropping both {@code COLLAPSES} rules failed no test in the suite at all.
 */
class ARuleAboutABuildingCarriesSomethingTest {

    private record Carries(String operation, String module) {}

    private static final List<Carries> CARRIES = List.of(
            new Carries("List.reverse", """
                    module demo
                    data NoItems
                    data Lines = List<Int>
                        invariant List.length(value) >= 1
                    behavior build : (xs: List<Int>) -> Lines | NoItems constructs Lines, NoItems
                    let build (xs) = {
                        guard List.length(xs) >= 1
                            else NoItems
                        Lines(List.reverse(xs))
                    }
                    """),
            new Carries("List.sort", """
                    module demo
                    data NoItems
                    data Lines = List<Int>
                        invariant List.length(value) >= 1
                    behavior build : (xs: List<Int>) -> Lines | NoItems constructs Lines, NoItems
                    let build (xs) = {
                        guard List.length(xs) >= 1
                            else NoItems
                        Lines(List.sort(xs))
                    }
                    """),
            new Carries("List.sortBy", """
                    module demo
                    data NoItems
                    data Row = { a: Int }
                    data Rows = List<Row>
                        invariant List.length(value) >= 1
                    behavior build : (xs: List<Row>) -> Rows | NoItems constructs Rows, NoItems
                    let build (xs) = {
                        guard List.length(xs) >= 1
                            else NoItems
                        Rows(List.sortBy(r -> r.a, xs))
                    }
                    """),
            new Carries("List.map", """
                    module demo
                    data NoItems
                    data Lines = List<Int>
                        invariant List.length(value) >= 1
                    behavior build : (xs: List<Int>) -> Lines | NoItems constructs Lines, NoItems
                    let build (xs) = {
                        guard List.length(xs) >= 1
                            else NoItems
                        Lines(List.map(x -> x + 1, xs))
                    }
                    """),
            new Carries("List.mapIndexed", """
                    module demo
                    data NoItems
                    data Lines = List<Int>
                        invariant List.length(value) >= 1
                    behavior build : (xs: List<Int>) -> Lines | NoItems constructs Lines, NoItems
                    let build (xs) = {
                        guard List.length(xs) >= 1
                            else NoItems
                        Lines(List.mapIndexed((i, x) -> i + x, xs))
                    }
                    """),
            new Carries("Map.mapValues", """
                    module demo
                    data NoEntries
                    data Index = Map<String, Int>
                        invariant Map.size(value) >= 1
                    behavior build : (m: Map<String, Int>) -> Index | NoEntries
                        constructs Index, NoEntries
                    let build (m) = {
                        guard Map.size(m) >= 1
                            else NoEntries
                        Index(Map.mapValues((k, v) -> v + 1, m))
                    }
                    """),
            new Carries("Map.updateIfPresent", """
                    module demo
                    data NoEntries
                    data Index = Map<String, Int>
                        invariant Map.size(value) >= 1
                    behavior build : (m: Map<String, Int>) -> Index | NoEntries
                        constructs Index, NoEntries
                    let build (m) = {
                        guard Map.size(m) >= 1
                            else NoEntries
                        Index(Map.updateIfPresent("a", v -> v + 1, m))
                    }
                    """),
            new Carries("List.filter", """
                    module demo
                    data TooMany
                    data Lines = List<Int>
                        invariant List.length(value) <= 10
                    behavior build : (xs: List<Int>) -> Lines | TooMany constructs Lines, TooMany
                    let build (xs) = {
                        guard List.length(xs) <= 10
                            else TooMany
                        Lines(List.filter(x -> x > 0, xs))
                    }
                    """),
            new Carries("List.distinct", """
                    module demo
                    data TooMany
                    data Lines = List<Int>
                        invariant List.length(value) <= 10
                    behavior build : (xs: List<Int>) -> Lines | TooMany constructs Lines, TooMany
                    let build (xs) = {
                        guard List.length(xs) <= 10
                            else TooMany
                        Lines(List.distinct(xs))
                    }
                    """),
            new Carries("List.distinctBy", """
                    module demo
                    data TooMany
                    data Row = { a: Int }
                    data Rows = List<Row>
                        invariant List.length(value) <= 10
                    behavior build : (xs: List<Row>) -> Rows | TooMany constructs Rows, TooMany
                    let build (xs) = {
                        guard List.length(xs) <= 10
                            else TooMany
                        Rows(List.distinctBy(r -> r.a, xs))
                    }
                    """),
            new Carries("List.take", """
                    module demo
                    data TooMany
                    data Lines = List<Int>
                        invariant List.length(value) <= 10
                    behavior build : (xs: List<Int>) -> Lines | TooMany constructs Lines, TooMany
                    let build (xs) = {
                        guard List.length(xs) <= 10
                            else TooMany
                        Lines(List.take(3, xs))
                    }
                    """),
            new Carries("List.drop", """
                    module demo
                    data TooMany
                    data Lines = List<Int>
                        invariant List.length(value) <= 10
                    behavior build : (xs: List<Int>) -> Lines | TooMany constructs Lines, TooMany
                    let build (xs) = {
                        guard List.length(xs) <= 10
                            else TooMany
                        Lines(List.drop(3, xs))
                    }
                    """),
            new Carries("List.filterMap", """
                    module demo
                    data TooMany
                    data Lines = List<Int>
                        invariant List.length(value) <= 10
                    behavior build : (xs: List<Int>) -> Lines | TooMany constructs Lines, TooMany
                    let build (xs) = {
                        guard List.length(xs) <= 10
                            else TooMany
                        Lines(List.filterMap(x -> List.get(0, [x]), xs))
                    }
                    """),
            new Carries("Map.filterEntries", """
                    module demo
                    data TooMany
                    data Index = Map<String, Int>
                        invariant Map.size(value) <= 10
                    behavior build : (m: Map<String, Int>) -> Index | TooMany constructs Index, TooMany
                    let build (m) = {
                        guard Map.size(m) <= 10
                            else TooMany
                        Index(Map.filterEntries((k, v) -> v > 0, m))
                    }
                    """),
            new Carries("Map.remove", """
                    module demo
                    data TooMany
                    data Index = Map<String, Int>
                        invariant Map.size(value) <= 10
                    behavior build : (m: Map<String, Int>) -> Index | TooMany constructs Index, TooMany
                    let build (m) = {
                        guard Map.size(m) <= 10
                            else TooMany
                        Index(Map.remove("a", m))
                    }
                    """),
            new Carries("Map.intersection", """
                    module demo
                    data TooMany
                    data Index = Map<String, Int>
                        invariant Map.size(value) <= 10
                    behavior build : (a: Map<String, Int>, b: Map<String, Int>) -> Index | TooMany
                        constructs Index, TooMany
                    let build (a, b) = {
                        guard Map.size(a) <= 10
                            else TooMany
                        Index(Map.intersection(a, b))
                    }
                    """),
            new Carries("Map.difference", """
                    module demo
                    data TooMany
                    data Index = Map<String, Int>
                        invariant Map.size(value) <= 10
                    behavior build : (a: Map<String, Int>, b: Map<String, Int>) -> Index | TooMany
                        constructs Index, TooMany
                    let build (a, b) = {
                        guard Map.size(a) <= 10
                            else TooMany
                        Index(Map.difference(a, b))
                    }
                    """),
            new Carries("Set.filter", """
                    module demo
                    data TooMany
                    data Tags = Set<String>
                        invariant Set.size(value) <= 10
                    behavior build : (s: Set<String>) -> Tags | TooMany constructs Tags, TooMany
                    let build (s) = {
                        guard Set.size(s) <= 10
                            else TooMany
                        Tags(Set.filter(t -> String.length(t) > 0, s))
                    }
                    """),
            new Carries("Set.map", """
                    module demo
                    data TooMany
                    data Tags = Set<String>
                        invariant Set.size(value) <= 10
                    behavior build : (s: Set<String>) -> Tags | TooMany constructs Tags, TooMany
                    let build (s) = {
                        guard Set.size(s) <= 10
                            else TooMany
                        Tags(Set.map(t -> String.trim(t), s))
                    }
                    """),
            new Carries("Set.remove", """
                    module demo
                    data TooMany
                    data Tags = Set<String>
                        invariant Set.size(value) <= 10
                    behavior build : (s: Set<String>) -> Tags | TooMany constructs Tags, TooMany
                    let build (s) = {
                        guard Set.size(s) <= 10
                            else TooMany
                        Tags(Set.remove("a", s))
                    }
                    """),
            new Carries("Set.intersection", """
                    module demo
                    data TooMany
                    data Tags = Set<String>
                        invariant Set.size(value) <= 10
                    behavior build : (a: Set<String>, b: Set<String>) -> Tags | TooMany
                        constructs Tags, TooMany
                    let build (a, b) = {
                        guard Set.size(a) <= 10
                            else TooMany
                        Tags(Set.intersection(a, b))
                    }
                    """),
            new Carries("Set.difference", """
                    module demo
                    data TooMany
                    data Tags = Set<String>
                        invariant Set.size(value) <= 10
                    behavior build : (a: Set<String>, b: Set<String>) -> Tags | TooMany
                        constructs Tags, TooMany
                    let build (a, b) = {
                        guard Set.size(a) <= 10
                            else TooMany
                        Tags(Set.difference(a, b))
                    }
                    """));

    @Test
    void everyRuleHasAConstructionThatFiresIt() {
        Set<String> witnessed = CARRIES.stream().map(Carries::operation)
                .collect(Collectors.toCollection(TreeSet::new));
        assertEquals(new TreeSet<>(DischargeRules.builtNames()), witnessed,
                "a rule is registered with no program that discharges because of it, or the other way"
                        + " round");
    }

    @Test
    void eachRuleCarriesWhatItsProgramNeeds() {
        List<String> carriedNothing = new ArrayList<>();
        for (Carries c : CARRIES) {
            long warnings = Compiler.compileWithWarnings(c.module()).warnings().stream()
                    .filter(d -> d.severity() == Severity.WARNING).count();
            if (warnings > 0) {
                carriedNothing.add(c.operation());
            }
        }
        assertEquals(List.of(), carriedNothing,
                "the clause should discharge from what these constructions keep of the container they"
                        + " were built from, and does not");
    }
}
