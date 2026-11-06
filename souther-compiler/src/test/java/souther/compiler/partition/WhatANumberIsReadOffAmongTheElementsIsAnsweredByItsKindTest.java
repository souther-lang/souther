package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Extreme;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.ElementKey;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerm.AmongTheElements;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Compilation;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a number is read off, as an element of a container sees it, is answered by the kind of
 * number and not by where it is filed ({@link NumericTerm#amongTheElementsOf}): how often the
 * element's value occurs is filed inside the element and read off the elements beside it, and a
 * total over the container is read off every element as one number.
 */
class WhatANumberIsReadOffAmongTheElementsIsAnsweredByItsKindTest {

    private static final TermPath FS = TermPath.of("fs");

    private static final TermPath CURRENCY = FS.element().then("currency");

    private static final TermPath AMOUNT = FS.element().then("amount");

    private static final TermPath RATE = TermPath.of("rate");

    private static final ElementProjection AT_THE_CURRENCY =
            ElementProjection.ofFields(List.of("currency"));

    private static final ElementValue THE_AMOUNT =
            new ElementValue.Affine(LinearForm.atom(ElementProjection.ofFields(List.of("amount"))));

    private static final AmongTheElements UNDER_THE_CURRENCY =
            new AmongTheElements.ThoseUnderItsKey(List.of(FS), new ElementKey.At(AT_THE_CURRENCY),
                    null);

    /**
     * How often the element's value occurs, the end of its key's values, what its key's elements
     * come to and how often a value of the run occurs are filed inside the element and read off
     * the elements of its key.
     */
    @Test
    void aNumberOfTheElementsBesideItIsOfThoseUnderItsKey() {
        NumericTerm often = NumericTerm.Multiplicity.of(FS, CURRENCY);
        NumericTerm least = NumericTerm.ExtremeOfItsKey.of(FS, CURRENCY, AMOUNT, Extreme.LEAST);
        NumericTerm total = NumericTerm.GatheredUnderItsKey.of(FS.element(),
                new ElementKey.At(AT_THE_CURRENCY), THE_AMOUNT, Type.Prim.INT,
                NumericTerm.GatheredUnderItsKey.Gathering.TOTAL, null);
        NumericTerm occurs = NumericTerm.OccurrencesOfItsValue.of(
                new RunSource.ProjectedOccurrences(CURRENCY), null);
        for (NumericTerm each : List.of(often, least, total, occurs)) {
            assertEquals(UNDER_THE_CURRENCY, each.amongTheElementsOf(FS), each::toString);
            assertEquals(AmongTheElements.NONE_OF_THEM,
                    each.amongTheElementsOf(TermPath.of("gs")), each::toString);
        }
    }

    /** Kept by a statement, a number of a key's elements is of those of them the statement
     *  keeps. */
    @Test
    void aNumberOfTheKeptElementsSaysWhatKeepsThem() {
        Proposition present = new Proposition.Present(new DecisionSubject.AnInput(AMOUNT), true);
        KeptOccurrences kept = new KeptOccurrences(new DecisionSubject.AnInput(FS), present,
                AStatementAtARow.of(present, "f", null));
        NumericTerm total = NumericTerm.GatheredUnderItsKey.of(FS.element(),
                new ElementKey.At(AT_THE_CURRENCY), THE_AMOUNT, Type.Prim.INT,
                NumericTerm.GatheredUnderItsKey.Gathering.TOTAL, kept);
        assertEquals(new AmongTheElements.ThoseUnderItsKey(List.of(FS),
                        new ElementKey.At(AT_THE_CURRENCY), kept),
                total.amongTheElementsOf(FS));
    }

    /**
     * Across the lists inside the elements of an outer list, how often a value occurs in one
     * list is read off that list alone, and so off the outer element holding it; what is
     * gathered under a value of all of them is read across every list, as an element of either
     * sees it.
     */
    @Test
    void acrossTheListsOfAnOuterListANumberSaysWhichItIsReadAcross() {
        TermPath ds = TermPath.of("ds");
        TermPath forecasts = ds.element().then("forecasts");
        TermPath place = forecasts.element().then("currency");
        NumericTerm often = NumericTerm.Multiplicity.of(forecasts, place);
        assertEquals(AmongTheElements.IT_ALONE, often.amongTheElementsOf(ds));
        assertEquals(new AmongTheElements.ThoseUnderItsKey(List.of(forecasts),
                new ElementKey.At(AT_THE_CURRENCY), null), often.amongTheElementsOf(forecasts));
        NumericTerm total = NumericTerm.GatheredUnderItsKey.of(forecasts.element(),
                new ElementKey.At(AT_THE_CURRENCY), THE_AMOUNT, Type.Prim.INT,
                NumericTerm.GatheredUnderItsKey.Gathering.TOTAL, null);
        AmongTheElements acrossBoth = new AmongTheElements.ThoseUnderItsKey(
                List.of(ds, forecasts), new ElementKey.At(AT_THE_CURRENCY), null);
        assertEquals(acrossBoth, total.amongTheElementsOf(ds));
        assertEquals(acrossBoth, total.amongTheElementsOf(forecasts));
    }

    /**
     * A product is read off what each of its numbers is read off, whichever factor comes
     * first: the element's amount times a rate outside it is read off the element and something
     * beside it, and so is how often its value occurs times the rate.
     */
    @Test
    void aProductIsReadOffWhatEachOfItsNumbersIs() {
        LinearForm<NumericTerm> amount = LinearForm.atom(new NumericTerm.ValueOf(AMOUNT));
        LinearForm<NumericTerm> rate = LinearForm.atom(new NumericTerm.ValueOf(RATE));
        LinearForm<NumericTerm> fee = LinearForm.atom(
                new NumericTerm.ValueOf(FS.element().then("fee")));
        assertEquals(AmongTheElements.OTHERWISE,
                NumericTerm.ProductOf.of(amount, rate).amongTheElementsOf(FS));
        assertEquals(AmongTheElements.OTHERWISE,
                NumericTerm.ProductOf.of(rate, amount).amongTheElementsOf(FS));
        assertEquals(AmongTheElements.IT_ALONE,
                NumericTerm.ProductOf.of(amount, fee).amongTheElementsOf(FS));
        assertEquals(AmongTheElements.NONE_OF_THEM, NumericTerm.ProductOf.of(rate,
                LinearForm.atom(new NumericTerm.ValueOf(TermPath.of("tax"))))
                .amongTheElementsOf(FS));
        NumericTerm often = NumericTerm.Multiplicity.of(FS, CURRENCY);
        assertEquals(AmongTheElements.OTHERWISE,
                NumericTerm.ProductOf.of(LinearForm.atom(often), rate).amongTheElementsOf(FS));
    }

    /**
     * Composing a container chooses what is read off its own elements: the element, how often
     * its value occurs among them, a total of them. Not a place holding them, a number read
     * across every occurrence of the container, or one read off something else as well.
     */
    @Test
    void onlyANumberOfTheContainersOwnElementsIsReadOffNothingButThem() {
        TermPath ds = TermPath.of("ds");
        TermPath forecasts = ds.element().then("forecasts");
        NumericTerm acrossTheDesks = NumericTerm.GatheredUnderItsKey.of(forecasts.element(),
                new ElementKey.At(AT_THE_CURRENCY), THE_AMOUNT, Type.Prim.INT,
                NumericTerm.GatheredUnderItsKey.Gathering.TOTAL, null);
        NumericTerm oneDesks = NumericTerm.Multiplicity.of(forecasts,
                forecasts.element().then("currency"));
        assertTrue(oneDesks.amongTheElementsOf(forecasts)
                .readsOnlyTheElementsOf(forecasts));
        assertFalse(acrossTheDesks.amongTheElementsOf(forecasts)
                .readsOnlyTheElementsOf(forecasts));
        for (NumericTerm each : List.of(new NumericTerm.ValueOf(AMOUNT),
                NumericTerm.Multiplicity.of(FS, CURRENCY))) {
            assertTrue(each.amongTheElementsOf(FS).readsOnlyTheElementsOf(FS),
                    each::toString);
        }
        for (NumericTerm each : List.of(new NumericTerm.ValueOf(FS),
                new NumericTerm.ValueOf(RATE),
                NumericTerm.ProductOf.of(LinearForm.atom(new NumericTerm.ValueOf(AMOUNT)),
                        LinearForm.atom(new NumericTerm.ValueOf(RATE))))) {
            assertFalse(each.amongTheElementsOf(FS).readsOnlyTheElementsOf(FS),
                    each::toString);
        }
    }

    /**
     * What keeps the elements a number is of is read off as well: kept by what each element
     * holds, the number is still read off nothing but the elements; kept by a value outside
     * them, it is read off that value too.
     */
    @Test
    void whatKeepsTheElementsIsReadOffWithThem() {
        Proposition byTheAmount = new Proposition.Present(new DecisionSubject.AnInput(AMOUNT),
                true);
        Proposition overTheRate = new Proposition.Present(new DecisionSubject.AnInput(RATE),
                true);
        for (Proposition keeping : List.of(byTheAmount, overTheRate)) {
            KeptOccurrences kept = new KeptOccurrences(new DecisionSubject.AnInput(FS), keeping,
                    AStatementAtARow.of(keeping, "f", null));
            NumericTerm total = NumericTerm.GatheredUnderItsKey.of(FS.element(),
                    new ElementKey.At(AT_THE_CURRENCY), THE_AMOUNT, Type.Prim.INT,
                    NumericTerm.GatheredUnderItsKey.Gathering.TOTAL, kept);
            assertEquals(keeping == byTheAmount,
                    total.amongTheElementsOf(FS).readsOnlyTheElementsOf(FS), total::toString);
            // And a relation of it turns on every place it is read off, the rate among them.
            RowDemand.Relational atLeastTen = new RowDemand.Relational(new TakenConstraint.Affine(
                    new LinearForm<>(ExactRatio.of(-10), Map.of(total, ExactRatio.ONE)), Rel.GE));
            assertEquals(keeping == overTheRate, atLeastTen.positions().contains(RATE),
                    atLeastTen::toString);
        }
    }

    /** A total of every element's amount is one number of all of them, and one of another
     *  list's is of none of them. */
    @Test
    void aNumberTakenOverTheContainerIsOfAllOfIt() {
        Compilation compilation = Compilation.ofSource("""
                module probe

                data Forecast = { currency: String, amount: Int }

                data Taken

                behavior take : (fs: List<Forecast>, gs: List<Forecast>) -> Taken
                """, "Main");
        RuleReadingSource rules = RuleReadings.of(compilation, compilation.modules().get(0));
        ValueName.Stdlib sum = ValueName.Stdlib.operation("List", "sum");
        NumericTerm overThese = NumericTerm.TakenOver.of(sum,
                new RunSource.ProjectedOccurrences(AMOUNT), Type.Prim.INT, rules.inners(),
                rules.symbols());
        NumericTerm overOthers = NumericTerm.TakenOver.of(sum,
                new RunSource.ProjectedOccurrences(TermPath.of("gs").element().then("amount")),
                Type.Prim.INT, rules.inners(), rules.symbols());
        assertEquals(new AmongTheElements.AllOfThem(List.of(FS)), overThese.amongTheElementsOf(FS));
        assertTrue(overThese.amongTheElementsOf(FS).readsOnlyTheElementsOf(FS));
        assertEquals(AmongTheElements.NONE_OF_THEM, overOthers.amongTheElementsOf(FS));
    }
}
