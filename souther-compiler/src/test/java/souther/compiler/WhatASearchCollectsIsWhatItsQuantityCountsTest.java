package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Quantity;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * {@link Quantity.HowManyDifferentBelow} counts what the search it stands for answers: for each
 * tree and map, the number its definition gives is the number of different values in the list the
 * search answers when the language runs it.
 *
 * <p>Both sides are asked of the same cases. The language is asked by an example whose output is
 * the number, and a reference written from the definition of the quantity — the root and the nodes
 * in the lists of every node reached, the entry of the map each one's key names where it holds
 * one, and the value taken of it — is asked in Java. They have to agree on every case, so that the
 * quantity read off a body means what the body computes, whatever composes a row toward it.
 */
class WhatASearchCollectsIsWhatItsQuantityCountsTest {

    private record Tree(String owner, List<Tree> reports) {

        static Tree of(String owner, Tree... reports) {
            return new Tree(owner, List.of(reports));
        }

        String written() {
            return "Node { owner = \"" + owner + "\", reports = ["
                    + String.join(", ", reports.stream().map(Tree::written).toList()) + "] }";
        }
    }

    private record Case(String says, Tree root, Map<String, String> currencies) {

        String written() {
            List<String> entries = new ArrayList<>();
            currencies.forEach((owner, currency) -> entries.add("(\"" + owner
                    + "\", Forecast { currency = \"" + currency + "\", amount = 1 })"));
            return entries.isEmpty() ? "(" + root.written() + ", noForecasts)"
                    : "(" + root.written() + ", Map.fromList([" + String.join(", ", entries)
                            + "]))";
        }
    }

    private static final Quantity.HowManyDifferentBelow QUANTITY =
            new Quantity.HowManyDifferentBelow(TermPath.of("node"), List.of("reports"),
                    TermPath.of("byOwner"), List.of("owner"), List.of("currency"));

    /** The number the definition of {@link #QUANTITY} gives for the tree and the map. */
    private static int counted(Tree root, Map<String, String> currencies) {
        Set<String> different = new HashSet<>();
        List<Tree> reached = new ArrayList<>(List.of(root));
        for (int at = 0; at < reached.size(); at++) {
            Tree node = reached.get(at);
            String value = currencies.get(node.owner());
            if (value != null) {
                different.add(value);
            }
            reached.addAll(node.reports());
        }
        return different.size();
    }

    private static Map<String, String> map(String... ownersAndCurrencies) {
        Map<String, String> out = new LinkedHashMap<>();
        for (int at = 0; at < ownersAndCurrencies.length; at += 2) {
            out.put(ownersAndCurrencies[at], ownersAndCurrencies[at + 1]);
        }
        return out;
    }

    private static final List<Case> CASES = List.of(
            new Case("nothing is held for any node", Tree.of("a", Tree.of("b")), map()),
            new Case("the root holds one", Tree.of("a", Tree.of("b")), map("a", "JPY")),
            new Case("only a child holds one, and the root holds none",
                    Tree.of("a", Tree.of("b")), map("b", "JPY")),
            new Case("only a grandchild holds one",
                    Tree.of("a", Tree.of("b", Tree.of("c"))), map("c", "JPY")),
            new Case("two nodes of one owner name one entry",
                    Tree.of("a", Tree.of("a"), Tree.of("a")), map("a", "JPY")),
            new Case("two entries of one value are one value",
                    Tree.of("a", Tree.of("b")), map("a", "JPY", "b", "JPY")),
            new Case("two entries of two values are two",
                    Tree.of("a", Tree.of("b")), map("a", "JPY", "b", "USD")),
            new Case("an entry no node names changes nothing",
                    Tree.of("a", Tree.of("b")), map("a", "JPY", "z", "USD")),
            new Case("an entry no node names changes nothing, with another reached",
                    Tree.of("a", Tree.of("b"), Tree.of("c")),
                    map("a", "JPY", "c", "JPY", "z", "USD")),
            new Case("three values from three levels",
                    Tree.of("a", Tree.of("b", Tree.of("c"))),
                    map("a", "JPY", "b", "USD", "c", "EUR")));

    @Test
    void theLanguageAnswersWhatTheDefinitionOfTheQuantityCounts() {
        StringBuilder source = new StringBuilder("""
                module probe.below

                data Forecast = { currency: String, amount: Int }
                data Node = { owner: String, reports: List<Node> }

                let noForecasts: Map<String, Forecast> = Map.empty

                let own (node: Node, byOwner: Map<String, Forecast>): List<Forecast> =
                    Map.get(node.owner, byOwner) |> Option.map(one -> [ one ])
                        |> Option.withDefault([])

                let under (node: Node, byOwner: Map<String, Forecast>): List<Forecast> =
                    List.fold((acc, r) -> acc ++ under(r, byOwner), own(node, byOwner),
                              node.reports)

                behavior howManyDiffer : (node: Node, byOwner: Map<String, Forecast>) -> Int
                let howManyDiffer (node, byOwner) =
                    Set.size(Set.fromList(List.map(.currency, under(node, byOwner))))

                example howManyDiffer
                """);
        for (Case each : CASES) {
            source.append("    | \"").append(each.says()).append("\" : ")
                    .append(each.written()).append(" -> ")
                    .append(counted(each.root(), each.currencies())).append('\n');
        }
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList());
    }

    /** The cases tell the quantity's parts apart: a reference that forgot one of them would
     *  count some case differently. */
    @Test
    void theCasesAreSensitiveToEachPartOfTheDefinition() {
        List<Integer> counts = CASES.stream()
                .map(each -> counted(each.root(), each.currencies())).toList();
        assertEquals(List.of(0, 1, 1, 1, 1, 1, 2, 1, 1, 3), counts);
    }
}
