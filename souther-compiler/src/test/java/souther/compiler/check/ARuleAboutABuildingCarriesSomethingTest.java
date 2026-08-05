package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A rule saying what a construction keeps of the container it was built from is worth having only
 * where something can travel through it: what the check states of a container it names by that
 * container's kind, so a rule between kinds carries nothing however true it is. Each rule the
 * building table has is held here to a program that discharges only because of it — remove the rule
 * and the clause is reported.
 */
class ARuleAboutABuildingCarriesSomethingTest {

    private record Carries(String operation, String module) {}

    private static final List<Carries> CARRIES = List.of(
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
                    """));

    @Test
    void eachRuleHasAConstructionItDischarges() {
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
