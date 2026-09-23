package souther.compiler.cst.contract;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code syntax/grammar.ebnf} is written in the notation its head defines.
 *
 * <p>The grammar is published for implementations that are not this one, and nothing here parses
 * Souther with it, so a production naming one that does not exist, or a parameter no production
 * takes, would reach every reader of it before anybody noticed. These are the questions the
 * notation's own sentences settle: what a name refers to, what a parameter is passed through, and
 * which productions are reachable.
 */
class TheGrammarIsWrittenInItsOwnNotationTest {

    private static final Grammar GRAMMAR = SyntaxContract.grammar();

    @Test
    void everyProductionHasOneName() {
        Set<String> seen = new HashSet<>();
        List<String> twice = new ArrayList<>();
        for (Grammar.Production each : GRAMMAR.productions()) {
            if (!seen.add(each.name())) {
                twice.add(each.name());
            }
        }
        assertEquals(List.of(), twice, "productions written twice");
    }

    @Test
    void everyReferenceNamesAProductionAndPassesWhatItTakes() {
        Set<String> names = new HashSet<>();
        GRAMMAR.productions().forEach(each -> names.add(each.name()));
        List<String> wrong = new ArrayList<>();
        for (Grammar.Production each : GRAMMAR.productions()) {
            for (Grammar.Reference reference : Grammar.references(each.body())) {
                if (!names.contains(reference.name())) {
                    wrong.add(each.name() + " refers to " + reference.name() + ", which is no production");
                    continue;
                }
                List<String> takes = GRAMMAR.production(reference.name()).parameters();
                for (String given : reference.arguments().keySet()) {
                    if (!takes.contains(given)) {
                        wrong.add(each.name() + " gives " + reference.name() + " " + given
                                + ", which it does not take");
                    }
                }
                for (String taken : takes) {
                    if (!reference.arguments().containsKey(taken)
                            && !each.parameters().contains(taken)) {
                        wrong.add(each.name() + " passes " + taken + " on to " + reference.name()
                                + " without taking it");
                    }
                }
            }
            for (Grammar.If condition : Grammar.conditionsOnParameters(each.body())) {
                if (!each.parameters().contains(condition.parameter())) {
                    wrong.add(each.name() + " asks for " + condition.parameter()
                            + ", which it does not take");
                }
            }
        }
        assertEquals(List.of(), wrong);
    }

    /**
     * Every production is reached from {@code source-file}, or is part of the lexical grammar,
     * which says what the tokens are and is reached by the text rather than by a production.
     */
    @Test
    void everyProductionIsReached() {
        Set<String> reached = new HashSet<>();
        List<String> pending = new ArrayList<>(GRAMMAR.region("lexical").productions());
        pending.add("source-file");
        while (!pending.isEmpty()) {
            String name = pending.removeLast();
            if (reached.add(name)) {
                for (Grammar.Reference reference : Grammar.references(GRAMMAR.production(name).body())) {
                    pending.add(reference.name());
                }
            }
        }
        List<String> unreached = new ArrayList<>();
        GRAMMAR.productions().forEach(each -> {
            if (!reached.contains(each.name())) {
                unreached.add(each.name());
            }
        });
        assertEquals(List.of(), unreached, "productions nothing reaches");
    }

    /**
     * Every production lies in a tagged region, which is how the specification shows it: each
     * construct's section includes its region, so a production outside every region is one the
     * specification never shows a reader.
     */
    @Test
    void everyProductionLiesInARegion() {
        Set<String> placed = new HashSet<>();
        GRAMMAR.regions().forEach(region -> placed.addAll(region.productions()));
        assertEquals(List.of(), GRAMMAR.productions().stream()
                .map(Grammar.Production::name)
                .filter(name -> !placed.contains(name))
                .toList(), "productions in no region");
    }

    /** And the reading read something, so the checks above are about a grammar. */
    @Test
    void theGrammarHasTheTreeItsCorpusIsWrittenIn() {
        assertTrue(GRAMMAR.nodes().contains("source-file"), "no node is named source-file");
        assertTrue(GRAMMAR.nodes().size() > 1, "the grammar marks no node");
    }
}
