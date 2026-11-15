package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.partition.CasesTheRowsTook.Kind;
import souther.compiler.partition.CasesTheRowsTook.NotAskable;
import souther.compiler.partition.CasesTheRowsTook.StatementShort;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the decision lacks is grouped once, by what the cases are cases of, and a statement is one
 * entry however its cases come.
 *
 * <p>A search that comes out finding a node owes the steps of finding one, and the same search
 * coming out empty may owe a step no row can be told from another: one statement with cases to
 * write rows for and cases no row can be asked for, which is one thing to act on. Asked of the
 * grouping directly, since which of these a model reaches is the model's.
 */
class AStatementThatLacksCasesIsOneEntryWhateverItsCasesAreTest {

    private static Proposition.SomeReachable search(String threshold) {
        TermPath node = TermPath.of("n");
        DecisionSubject below = new DecisionSubject.AnInput(node.then("below"));
        return new Proposition.SomeReachable(node, node, List.of("below"),
                new Proposition.Some(below, new Proposition.Truth(
                        new DecisionSubject.AnInput(node.then("below").element().then(threshold)),
                        true), true),
                Optional.empty(), true);
    }

    private static Set<CaseOfAStatement> unseen(CaseOfAStatement... cases) {
        return new LinkedHashSet<>(List.of(cases));
    }

    private static Set<NotAskable> notAskable(NotAskable... each) {
        return new LinkedHashSet<>(List.of(each));
    }

    @Test
    void aSearchWithCasesToWriteRowsForAndCasesNoRowCanBeAskedForIsOneEntryWithBoth() {
        Proposition.SomeReachable search = search("v");

        List<StatementShort> lacking = CasesTheRowsTook.lacking(
                unseen(new CaseOfAStatement.Search(search, CaseOfAStatement.Step.AT_THE_NODE),
                        new CaseOfAStatement.Search(search, CaseOfAStatement.Step.BELOW_IT)),
                notAskable(new NotAskable(search, Kind.A_NODE_A_SEARCH_REACHES)), Map.of());

        assertEquals(1, lacking.size(), lacking::toString);
        assertEquals(2, lacking.getFirst().unseen().size());
        assertTrue(lacking.getFirst().notAskable());
    }

    @Test
    void aSearchOnlyCasesNoRowCanBeAskedForIsAnEntryWithNoCases() {
        List<StatementShort> lacking = CasesTheRowsTook.lacking(unseen(),
                notAskable(new NotAskable(search("v"), Kind.A_NODE_A_SEARCH_REACHES)), Map.of());

        assertEquals(1, lacking.size(), lacking::toString);
        assertTrue(lacking.getFirst().unseen().isEmpty());
        assertTrue(lacking.getFirst().notAskable());
    }

    @Test
    void aSearchWithOnlyCasesToWriteRowsForIsNotSaidToHaveCasesNoRowCanBeAskedFor() {
        Proposition.SomeReachable search = search("v");

        List<StatementShort> lacking = CasesTheRowsTook.lacking(
                unseen(new CaseOfAStatement.Search(search, CaseOfAStatement.Step.BELOW_IT)),
                notAskable(), Map.of());

        assertEquals(1, lacking.size(), lacking::toString);
        assertFalse(lacking.getFirst().notAskable());
    }

    @Test
    void twoSearchesAreTwoEntriesAndAKindOfCaseIsNotMeltedIntoAnother() {
        Proposition.SomeReachable one = search("v");
        Proposition.SomeReachable other = search("w");

        List<StatementShort> lacking = CasesTheRowsTook.lacking(
                unseen(new CaseOfAStatement.Search(one, CaseOfAStatement.Step.BELOW_IT)),
                notAskable(new NotAskable(other, Kind.A_NODE_A_SEARCH_REACHES),
                        new NotAskable(one, Kind.THE_ORDER_OF_A_REPEATED_KEY)), Map.of());

        assertEquals(3, lacking.size(), lacking::toString);
        assertFalse(lacking.get(0).notAskable(), "the search the rows were short of");
        assertEquals(Kind.A_NODE_A_SEARCH_REACHES, lacking.get(1).kind());
        assertEquals(Kind.THE_ORDER_OF_A_REPEATED_KEY, lacking.get(2).kind());
    }

    @Test
    void anEntryLacksSomethingOrIsNotAnEntry() {
        assertThrows(IllegalArgumentException.class, () -> new StatementShort("s",
                search("v"), Kind.A_NODE_A_SEARCH_REACHES, List.of(), false, Optional.empty()));
    }
}
