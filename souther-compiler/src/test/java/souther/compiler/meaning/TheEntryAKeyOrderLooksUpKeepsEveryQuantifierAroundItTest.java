package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What it is for the entry a key order looks up to be there is said under every quantifier around
 * the lookup: a list the statement quantifies over from outside holds an element too, since a
 * statement over none looks nothing up and no order of the elements decides it.
 */
class TheEntryAKeyOrderLooksUpKeepsEveryQuantifierAroundItTest {

    private static final DecisionSubject ITEMS = new DecisionSubject.AnInput(TermPath.of("items"));
    private static final DecisionSubject ROWS = new DecisionSubject.AnInput(TermPath.of("rows"));
    private static final DecisionSubject ROW_SKU =
            new DecisionSubject.AnInput(TermPath.of("rows").element().then("sku"));
    private static final DecisionSubject ITEM_SKU =
            new DecisionSubject.AnInput(TermPath.of("items").element().then("sku"));
    private static final DecisionSubject ROW_OK =
            new DecisionSubject.AnInput(TermPath.of("rows").element().then("ok"));

    private static final Proposition.LastToHold LAST =
            new Proposition.LastToHold(ROWS, ROW_SKU, true);
    private static final Proposition SAME = new Proposition.SameValue(ROW_SKU, ITEM_SKU, true);

    /** The lookup is inside the quantifier over the items, and the restatement is too. */
    @Test
    void theListQuantifiedFromOutsideHoldsAnElementToo() {
        Proposition inner = new Proposition.Some(ROWS, Proposition.all(List.of(LAST,
                new Proposition.Truth(ROW_OK, true), SAME)), true);
        Proposition stated = new Proposition.Some(ITEMS, inner, true);

        Optional<Proposition> looked = Proposition.theEntryLookedUp(stated, LAST);

        Proposition entry = new Proposition.Some(ROWS, Proposition.all(List.of(LAST, SAME)), true);
        assertEquals(Optional.of(new Proposition.Some(ITEMS, entry, true)), looked);
    }

    /** With nothing around the quantifier nearest the lookup, that quantifier is all there is. */
    @Test
    void aQuantifierWithNoneAroundItIsTheWholeOfIt() {
        Proposition stated = new Proposition.Some(ROWS, Proposition.all(List.of(LAST,
                new Proposition.Truth(ROW_OK, true), SAME)), true);

        Optional<Proposition> looked = Proposition.theEntryLookedUp(stated, LAST);

        assertEquals(Optional.of(new Proposition.Some(ROWS,
                Proposition.all(List.of(LAST, SAME)), true)), looked);
    }
}
