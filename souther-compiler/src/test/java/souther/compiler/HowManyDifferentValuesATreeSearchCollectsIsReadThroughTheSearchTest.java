package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * How many different values a search down a tree collects, where each node adds the entry of an
 * input map its own key names, is read as that number — and not as a value the body worked out,
 * which nothing is then said of.
 *
 * <p>What it is about is the nodes the search reaches and the entries their keys pick, so it is no
 * number of the map's own entries: a map may hold an entry no node reaches, and that entry's value
 * changes nothing the search collects.
 */
class HowManyDifferentValuesATreeSearchCollectsIsReadThroughTheSearchTest {

    private static final String HEAD = """
            module probe.tree

            data Forecast = { currency: String, amount: Int }
            data Node = { owner: String, reports: List<Node> }

            let own (node: Node, byOwner: Map<String, Forecast>): List<Forecast> =
                Map.get(node.owner, byOwner) |> Option.map(one -> [ one ]) |> Option.withDefault([])

            let under (node: Node, byOwner: Map<String, Forecast>): List<Forecast> =
                List.fold((acc, r) -> acc ++ under(r, byOwner), own(node, byOwner), node.reports)

            """;

    /** The reasons a behavior's positions were left unread for, each with the position. */
    private static List<String> notRead(String behavior, String name) {
        Compilation compilation = Compilation.ofSource(HEAD + behavior, "Main");
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList());
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        List<String> said = new ArrayList<>();
        for (AdequacyReport.BehaviorReport each :
                AdequacyReport.of(compilation).modules().get(0).behaviors()) {
            if (each.name().equals(name)) {
                each.partition().notRead().forEach(one -> said.add(one.at() + " " + one.reason()));
            }
        }
        return said.stream().sorted().toList();
    }

    private static void relatesValuesNotADerivedOne(String condition) {
        List<String> said = notRead("""
                behavior f : (node: Node, byOwner: Map<String, Forecast>) -> Bool
                let f (node, byOwner) = %s
                """.formatted(condition), "f");

        // The values the nodes collect are the ones the rule relates, as the elements of a list
        // are; and the keys a node looks its entry up by, and the keys of the entries, are only
        // asked to be the same or not, so the rule draws no line on them either.
        assertEquals(List.of(
                "byOwner[*].currency RULE_RELATING_TWO_VALUES",
                "byOwner[key] RULE_RELATING_TWO_VALUES",
                "node.owner RULE_RELATING_TWO_VALUES"), said);
    }

    @Test
    void theDifferentValuesOfWhatASearchCollectsAreReadWhenAllOfThemAreAskedToBeOne() {
        relatesValuesNotADerivedOne(
                "Set.size(Set.fromList(List.map(.currency, under(node, byOwner)))) == 1");
    }

    @Test
    void theSameNumberIsReadWhateverWayItIsAsked() {
        relatesValuesNotADerivedOne(
                "List.length(List.distinct(List.map(.currency, under(node, byOwner)))) >= 2");
    }

    /**
     * A guard before it that some node reached has an entry is a way that states the same lookup,
     * and the rule after it is read the same: the keys are left as they were without the guard.
     */
    @Test
    void theSameNumberIsReadAfterAGuardThatSomeEntryIsCollected() {
        List<String> said = notRead("""
                data Mixed = { n: Int }

                behavior g : (node: Node, byOwner: Map<String, Forecast>) -> Int | Mixed
                let g (node, byOwner) = {
                    let collected = under(node, byOwner)
                    guard Bool.not(List.isEmpty(collected)) else Mixed { n = 0 }
                    guard Set.size(Set.fromList(List.map(.currency, collected))) == 1
                        else Mixed { n = 1 }
                    1
                }
                """, "g");

        assertEquals(List.of(
                "byOwner[*].currency RULE_RELATING_TWO_VALUES",
                "byOwner[key] RULE_RELATING_TWO_VALUES",
                "node.owner RULE_RELATING_TWO_VALUES"), said);
    }

    @Test
    void theSameNumberIsReadThroughALet() {
        relatesValuesNotADerivedOne("""
                {
                    let collected = under(node, byOwner)
                    Set.size(Set.fromList(List.map(.currency, collected))) == 1
                }""");
    }
}
