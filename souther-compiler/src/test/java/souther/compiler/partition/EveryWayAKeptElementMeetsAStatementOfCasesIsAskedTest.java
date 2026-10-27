package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A statement saying only which cases positions of an element are in is met in every way it can
 * be, and which way a row is written in is not chosen where the statement is read.
 *
 * <p>A way is one case at each position it names, because a plan writes one case of a sum. A row
 * that already asks a case of the same position meets the statement in the ways that stand beside
 * it, and only those: a way that conflicts is one way gone, and the statement is unmet only where
 * every way has.
 */
class EveryWayAKeptElementMeetsAStatementOfCasesIsAskedTest {

    private static final TermPath LINES = TermPath.of("lines");
    private static final TermPath RELATED = LINES.element().then("related");
    private static final TermPath SIZE = LINES.element().then("size");

    @Test
    void aStatementOfSeveralCasesIsMetInEachOfThem() {
        KeptOccurrences.CasesAsked asked = asked(inCases(RELATED, "Account", "Deal")).orElseThrow();
        assertEquals(List.of(only(RELATED, "Account"), only(RELATED, "Deal")), asked.ways());
        assertEquals(List.of(RELATED), asked.positions());
    }

    @Test
    void aWayMeetingAnyOfSeveralStatementsIsAWayOfAnyOfThem() {
        Proposition stated = Proposition.any(List.of(inCases(RELATED, "Account"),
                inCases(SIZE, "Big")));
        KeptOccurrences.CasesAsked asked = asked(stated).orElseThrow();
        assertEquals(List.of(only(RELATED, "Account"), only(SIZE, "Big")), asked.ways());
        assertEquals(List.of(RELATED, SIZE), asked.positions());
    }

    @Test
    void aWayMeetingAllOfSeveralStatementsStandsBesideAWayOfEach() {
        Proposition stated = Proposition.all(List.of(inCases(RELATED, "Account", "Deal"),
                inCases(SIZE, "Big")));
        KeptOccurrences.CasesAsked asked = asked(stated).orElseThrow();
        assertEquals(2, asked.ways().size(), asked::toString);
        for (Requirements way : asked.ways()) {
            assertEquals(only(SIZE, "Big").at(SIZE), way.at(SIZE));
            assertTrue(way.at(RELATED) != null && way.at(RELATED).only() != null, way::toString);
        }
    }

    @Test
    void waysAskingTwoCasesOfOnePositionAreNoWay() {
        Proposition stated = Proposition.all(List.of(inCases(RELATED, "Account", "Deal"),
                inCases(RELATED, "Deal", "Lead")));
        assertEquals(List.of(only(RELATED, "Deal")), asked(stated).orElseThrow().ways());
        assertTrue(asked(Proposition.all(List.of(inCases(RELATED, "Account"),
                inCases(RELATED, "Deal")))).isEmpty());
    }

    @Test
    void aStatementOfAnythingButCasesIsNoStatementOfCases() {
        Proposition other = new Proposition.Truth(new DecisionSubject.AnInput(SIZE), true);
        assertTrue(asked(other).isEmpty());
        assertTrue(asked(Proposition.any(List.of(inCases(RELATED, "Account"), other))).isEmpty());
        assertTrue(asked(inCases(RELATED, "Account").denied()).isEmpty());
    }

    /**
     * A row that asks the position a case meets the statement in the ways beside that case, and a
     * way that conflicts with it is gone while the others stand — not the first way, whichever it
     * is.
     */
    @Test
    void aRowAskingOneCaseMeetsTheStatementInTheWaysBesideIt() {
        KeptOccurrences.CasesAsked asked = asked(inCases(RELATED, "Account", "Deal")).orElseThrow();
        Requirements row = only(RELATED, "Deal");
        List<Requirements> beside = new ArrayList<>();
        for (Requirements way : asked.ways()) {
            if (row.merge(way) instanceof Requirements.Merge.Merged(Requirements both)) {
                beside.add(both);
            }
        }
        assertEquals(List.of(row), beside);
        Requirements none = only(RELATED, "Lead");
        assertTrue(asked.ways().stream().noneMatch(way -> none.merge(way)
                instanceof Requirements.Merge.Merged), "no way stands beside a case it does not name");
    }

    /** A case of the position's own, whatever else says the same, is one way and is counted once. */
    @Test
    void aWayTwoStatementsGiveIsCountedOnce() {
        Proposition stated = Proposition.any(List.of(inCases(RELATED, "Account", "Deal"),
                inCases(RELATED, "Deal", "Lead")));
        assertEquals(List.of(only(RELATED, "Account"), only(RELATED, "Deal"),
                only(RELATED, "Lead")), asked(stated).orElseThrow().ways());
    }

    /**
     * A field of one case of the element is there only where the element is that case, so a way
     * reading it says so, and no way reads it beside a field of another case.
     */
    @Test
    void aFieldOfOneCaseIsAskedWhereTheElementIsThatCase() {
        TermPath callFlag = LINES.element().refine(refinement("Call")).then("flag");
        TermPath emailFlag = LINES.element().refine(refinement("Email")).then("flag");
        Requirements way = asked(inCases(callFlag, "Big")).orElseThrow().ways().getFirst();
        assertEquals(cases("Call"), way.at(LINES.element()), way::toString);
        assertEquals(cases("Big"), way.at(callFlag.position()), way::toString);
        assertTrue(asked(Proposition.all(List.of(inCases(callFlag, "Big"),
                inCases(emailFlag, "Big")))).isEmpty());
        assertTrue(asked(Proposition.all(List.of(inCases(callFlag, "Big"),
                inCases(callFlag, "Big")))).isPresent());
    }

    private static Refinement refinement(String leaf) {
        return Refinement.of(new Case.SumCase(
                TypeSymbols.declared(new TypeKey("probe", leaf)), true));
    }

    private static Optional<KeptOccurrences.CasesAsked> asked(Proposition stated) {
        return new KeptOccurrences(new DecisionSubject.AnInput(LINES), stated,
                AStatementAtARow.of(stated, "f", null)).casesAsked();
    }

    private static Proposition inCases(TermPath at, String... leaves) {
        return new Proposition.InCases(new DecisionSubject.AnInput(at), cases(leaves), true);
    }

    private static Requirements only(TermPath at, String leaf) {
        return Requirements.NONE.and(at, cases(leaf));
    }

    private static CasesLeft cases(String... leaves) {
        List<Refinement> atoms = new ArrayList<>();
        for (String leaf : leaves) {
            atoms.add(Refinement.of(new Case.SumCase(
                    TypeSymbols.declared(new TypeKey("probe", leaf)), true)));
        }
        return CasesLeft.ofEach(atoms);
    }
}
