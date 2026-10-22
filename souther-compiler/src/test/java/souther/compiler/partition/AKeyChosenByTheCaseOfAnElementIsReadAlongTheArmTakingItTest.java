package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.DeclarationAccess;
import souther.compiler.check.Extreme;
import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.ElementKey;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.LinearForm;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A key chosen by the case of a place of each element is read, for each element, along the way
 * of the arm its case is taken by, and along no other: the elements of a run of activities
 * related to an account directly or through a deal are filed under the account whichever way
 * each reaches it.
 *
 * <p>The term is built by hand, so what is held here is the reading of rows and not the walk that
 * finds such a key in a body. What the reading owes is the program's answer: an element of one
 * case is never asked for a field of another, two elements holding one key are one key whichever
 * arm read each, and an element the statement keeping them drops is filed under no key — while
 * one no arm takes that is handed in all the same is not quietly left out.
 */
class AKeyChosenByTheCaseOfAnElementIsReadAlongTheArmTakingItTest {

    private static final TermPath ACTS = TermPath.of("acts");
    private static final TermPath ELEMENTS = ACTS.element();

    private static final TypeSymbol ACT = TypeSymbols.declared(new TypeKey("probe", "Act"));
    private static final TypeSymbol TO_ACCOUNT =
            TypeSymbols.declared(new TypeKey("probe", "ToAccount"));
    private static final TypeSymbol TO_DEAL = TypeSymbols.declared(new TypeKey("probe", "ToDeal"));
    private static final TypeSymbol TO_LEAD = TypeSymbols.declared(new TypeKey("probe", "ToLead"));

    private static final ElementProjection RELATED = ElementProjection.ofFields(List.of("related"));
    private static final ElementProjection ON = ElementProjection.ofFields(List.of("on"));
    private static final ElementProjection ACCOUNT_KEY =
            RELATED.narrowedTo(caseOf(TO_ACCOUNT)).then("accountId");
    private static final ElementProjection DEAL_KEY =
            RELATED.narrowedTo(caseOf(TO_DEAL)).then("accountId");

    private static final Carrier WHOLE = Carrier.ofValue(Type.Prim.INT, DeclarationAccess.NONE);

    private static CasesLeft caseOf(TypeSymbol leaf) {
        return CasesLeft.of(Refinement.of(new Case.SumCase(leaf, true)));
    }

    /** {@code ToAccount { accountId } -> accountId | ToDeal { accountId } -> accountId}. */
    private static final ElementKey KEY = new ElementKey.ByCase(RELATED, List.of(
            new ElementKey.ByCase.Arm(caseOf(TO_ACCOUNT), ACCOUNT_KEY),
            new ElementKey.ByCase.Arm(caseOf(TO_DEAL), DEAL_KEY)));

    /** The elements related to an account, which are the ones an arm answers a key for. */
    private static final Proposition RELATED_TO_AN_ACCOUNT = new Proposition.InCases(
            new DecisionSubject.AnInput(ELEMENTS.then("related")),
            CasesLeft.ofEach(List.of(Refinement.of(new Case.SumCase(TO_ACCOUNT, true)),
                    Refinement.of(new Case.SumCase(TO_DEAL, true)))), true);

    private static final KeptOccurrences KEPT = new KeptOccurrences(
            new DecisionSubject.AnInput(ACTS), RELATED_TO_AN_ACCOUNT,
            AStatementAtARow.of(RELATED_TO_AN_ACCOUNT, "f", null));

    private static final NumericTerm.GatheredUnderItsKey LEAST =
            NumericTerm.GatheredUnderItsKey.of(ELEMENTS, KEY,
                    new ElementValue.Affine(LinearForm.atom(ON)), Type.Prim.INT,
                    new NumericTerm.GatheredUnderItsKey.Gathering.End(Extreme.LEAST), KEPT);

    private static final TermOrders ORDERS = TermOrdersFixtures.computed(LEAST, WHOLE, WHOLE,
            Map.of(ACCOUNT_KEY, Carrier.TEXT, DEAL_KEY, Carrier.TEXT, ON, WHOLE));

    private static ObservedValue act(ObservedValue related, long on) {
        return new ObservedValue.Constructed(ACT, Map.of("related", related,
                "on", new ObservedValue.Integer(on)));
    }

    private static ObservedValue toAccount(String account, long on) {
        return act(new ObservedValue.Constructed(TO_ACCOUNT,
                Map.of("accountId", new ObservedValue.Text(account))), on);
    }

    private static ObservedValue toDeal(String account, long on) {
        return act(new ObservedValue.Constructed(TO_DEAL,
                Map.of("accountId", new ObservedValue.Text(account),
                        "deal", new ObservedValue.Text("d"))), on);
    }

    private static ObservedValue toLead(long on) {
        return act(new ObservedValue.Constructed(TO_LEAD,
                Map.of("lead", new ObservedValue.Text("l"))), on);
    }

    private static TermOrders.Neighbouring<String> least(long value) {
        return new TermOrders.Neighbouring.Read<>(new NumericTerm.Reading.Number(Count.of(value)));
    }

    /** Elements of one case alone are filed under what that case's arm reads. */
    @Test
    void theElementsOfEitherCaseAloneAreFiledUnderWhatItsArmReads() {
        List<ObservedValue> accounts = List.of(toAccount("a", 5), toAccount("a", 3),
                toAccount("b", 9));
        assertEquals(least(3), TermOrdersFixtures.numberOf(ORDERS, accounts.get(0), accounts));
        assertEquals(least(9), TermOrdersFixtures.numberOf(ORDERS, accounts.get(2), accounts));
        List<ObservedValue> deals = List.of(toDeal("a", 5), toDeal("b", 4), toDeal("a", 7));
        assertEquals(least(5), TermOrdersFixtures.numberOf(ORDERS, deals.get(2), deals));
        assertEquals(least(4), TermOrdersFixtures.numberOf(ORDERS, deals.get(1), deals));
    }

    /** Two elements holding one key are one key, whichever arm each was read by. */
    @Test
    void elementsOfTwoCasesHoldingOneKeyAreOneKey() {
        List<ObservedValue> acts = List.of(toAccount("a", 5), toDeal("a", 2), toDeal("b", 1),
                toAccount("b", 8));
        assertEquals(least(2), TermOrdersFixtures.numberOf(ORDERS, acts.get(0), acts));
        assertEquals(least(2), TermOrdersFixtures.numberOf(ORDERS, acts.get(1), acts));
        assertEquals(least(1), TermOrdersFixtures.numberOf(ORDERS, acts.get(3), acts));
    }

    /**
     * An element is asked its case, then the key of the arm taking it: a field of another case is
     * never asked of it, since an element of one case holding nothing there is an answer about
     * its case and not a field left unwritten.
     */
    @Test
    void anElementIsAskedTheKeyOfTheArmItsCaseIsTakenByAndNoOther() {
        List<ObservedValue> acts = List.of(toAccount("a", 5), toDeal("a", 2));
        List<ElementProjection> askedOfTheDeal = new ArrayList<>();
        List<Function<ElementProjection, TermOrders.Holding<String>>> each = new ArrayList<>();
        each.add(TermOrdersFixtures.holding(ORDERS, acts.get(0)));
        Function<ElementProjection, TermOrders.Holding<String>> deal =
                TermOrdersFixtures.holding(ORDERS, acts.get(1));
        each.add(field -> {
            askedOfTheDeal.add(field);
            return deal.apply(field);
        });
        assertEquals(least(2), ORDERS.together(each).numberOf(each.get(1)));
        assertTrue(Set.of(RELATED, DEAL_KEY, ON).containsAll(askedOfTheDeal),
                () -> "a deal is asked its case, its own key and its number, and not "
                        + askedOfTheDeal);
        assertTrue(askedOfTheDeal.contains(DEAL_KEY), "a deal's key is read where it is");
    }

    /**
     * An element no arm takes, handed to the key all the same, is no element whose key is known:
     * it stops every key, as an element whose key is no value does. Leaving it out is the
     * statement's to say, and only where it says so.
     */
    @Test
    void anElementNoArmTakesStopsEveryKeyRatherThanBeingLeftOut() {
        List<ObservedValue> acts = List.of(toAccount("a", 5), toLead(1));
        assertEquals(new TermOrders.Neighbouring.Read<>(new NumericTerm.Reading.NotNumber()),
                TermOrdersFixtures.numberOf(ORDERS, acts.get(0), acts));
    }

    /**
     * Read back from the elements a row holds, the ones the statement drops are filed under no
     * key, and nothing about their key is asked: the key and the number of an activity related
     * to no account are no part of any account's least.
     */
    @Test
    void anElementTheStatementDropsIsReadBackUnderNoKey() {
        List<ObservedValue> acts = List.of(toLead(1), toAccount("a", 5), toDeal("a", 4));
        assertEquals(new Generator.RealizationReadback.AtRequestedPlace(),
                Generator.readBack(ORDERS, acts, Count.of(4)));
        assertInstanceOf(Generator.RealizationReadback.Elsewhere.class,
                Generator.readBack(ORDERS, acts, Count.of(1)),
                "the lead's 1 is kept by no account");
    }

    /**
     * Read at a row with one element chosen: an element the statement keeps comes to its key's
     * least among the kept ones, and one it drops is filed under no key, which is nothing
     * written there — not an element whose key could not be read.
     */
    @Test
    void aRowsChosenElementIsReadUnderItsKeyOnlyWhereItIsKept() {
        List<ObservedValue> acts = List.of(toLead(1), toAccount("a", 5), toDeal("a", 4));
        assertEquals(new WhatATermRead.Number(Count.of(4)),
                WhatATermRead.underItsKey(ORDERS, new Acts(acts, 1)));
        assertEquals(new WhatATermRead.Number(Count.of(4)),
                WhatATermRead.underItsKey(ORDERS, new Acts(acts, 2)));
        assertEquals(new WhatATermRead.NothingWrittenThere(),
                WhatATermRead.underItsKey(ORDERS, new Acts(acts, 0)),
                "a lead is filed under no account");
    }

    /**
     * A key chosen by case pairs each case with a way that case has: a way reading another case's
     * field, or two arms taking one case, are no key at all. Arms reading one way are that way.
     */
    @Test
    void aKeyPairingACaseWithAnotherCasesFieldIsRefused() {
        assertThrows(IllegalArgumentException.class, () -> new ElementKey.ByCase(RELATED, List.of(
                new ElementKey.ByCase.Arm(caseOf(TO_ACCOUNT), DEAL_KEY),
                new ElementKey.ByCase.Arm(caseOf(TO_DEAL), ACCOUNT_KEY))));
        assertThrows(IllegalArgumentException.class, () -> new ElementKey.ByCase(RELATED, List.of(
                new ElementKey.ByCase.Arm(caseOf(TO_ACCOUNT), ACCOUNT_KEY),
                new ElementKey.ByCase.Arm(caseOf(TO_ACCOUNT), ON))));
        assertEquals(new ElementKey.At(ON), ElementKey.byCase(RELATED, List.of(
                new ElementKey.ByCase.Arm(caseOf(TO_ACCOUNT), ON),
                new ElementKey.ByCase.Arm(caseOf(TO_DEAL), ON))));
    }

    /** One list of activities, read with the one at {@code chosen} chosen. */
    private record Acts(List<ObservedValue> each, int chosen)
            implements BorderQuantity.Observation {

        @Override
        public WalkResult<ObservationAtPoint> at(TermPath path) {
            ElementProjection within = ElementProjection.below(ELEMENTS, path);
            ObservedValue held = within == null ? null
                    : within.in(each.get(chosen), _ -> List.of());
            return WalkResult.reached(held == null ? new ObservationAtPoint.WroteNothing()
                    : new ObservationAtPoint.Value(held));
        }

        @Override
        public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
            throw new UnsupportedOperationException("a key's number reads its elements one by one");
        }

        @Override
        public WalkResult<List<BorderQuantity.Observation>> eachElementOf(TermPath container) {
            List<BorderQuantity.Observation> out = new ArrayList<>();
            for (int at = 0; at < each.size(); at++) {
                out.add(new Acts(each, at));
            }
            return WalkResult.reached(out);
        }
    }
}
