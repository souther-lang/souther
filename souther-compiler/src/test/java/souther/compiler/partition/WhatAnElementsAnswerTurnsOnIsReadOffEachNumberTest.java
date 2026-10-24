package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Extreme;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.ElementKey;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.numeric.LinearForm;
import souther.compiler.query.Compilation;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Optional;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What an element's answer turns on, among the elements of a container held as groups under one
 * value, is read off each number the answer reads, of every part the number is made of: where it
 * is read among, the key it is gathered under, the value it gathers and the statement keeping the
 * elements it is of ({@link AStatementAtARow#readOf}). A container is chosen by what a row holding
 * one group alone answers only where nothing turns on more than the group, and a group is listed
 * under one value for all of them only where nothing reads the value itself.
 */
class WhatAnElementsAnswerTurnsOnIsReadOffEachNumberTest {

    private static final TermPath FS = TermPath.of("fs");

    private static final TermPath CURRENCY = FS.element().then("currency");

    private static final TermPath AMOUNT = FS.element().then("amount");

    private static final ElementProjection AT_THE_CURRENCY =
            ElementProjection.ofFields(List.of("currency"));

    private static final ElementValue THE_AMOUNT =
            new ElementValue.Affine(LinearForm.atom(ElementProjection.ofFields(List.of("amount"))));

    private static final AStatementAtARow.WhatItReads THE_ELEMENT =
            new AStatementAtARow.WhatItReads(AStatementAtARow.TurnsOn.THE_ELEMENT, false);

    private static final AStatementAtARow.WhatItReads THOSE_UNDER_IT =
            new AStatementAtARow.WhatItReads(AStatementAtARow.TurnsOn.THOSE_UNDER_ITS_VALUE,
                    false);

    private static AStatementAtARow.WhatItReads read(NumericTerm term, TermPath under) {
        return AStatementAtARow.readOf(term, FS, under, Optional.empty());
    }

    /**
     * Grouped over every element of the lists inside the elements of an outer list, what is
     * gathered under a value of all of them turns on those holding it, as it does over one
     * list; read with the elements of one list grouped, it turns on the other lists' too. How
     * often a value occurs in one of the lists turns on which list it is.
     */
    @Test
    void whatTheElementsOfAValueAcrossTheListsComeToTurnsOnThoseHoldingIt() {
        TermPath ds = TermPath.of("ds");
        TermPath forecasts = ds.element().then("forecasts");
        TermPath currency = forecasts.element().then("currency");
        NumericTerm total = NumericTerm.GatheredUnderItsKey.of(forecasts.element(),
                new ElementKey.At(AT_THE_CURRENCY), THE_AMOUNT, Type.Prim.INT,
                NumericTerm.GatheredUnderItsKey.Gathering.TOTAL, null);
        assertEquals(THOSE_UNDER_IT,
                AStatementAtARow.readOf(total, forecasts, currency, Optional.of(ds)));
        assertEquals(AStatementAtARow.TurnsOn.OTHER_ELEMENTS,
                AStatementAtARow.readOf(total, forecasts, currency, Optional.empty()).turnsOn());
        NumericTerm often = NumericTerm.Multiplicity.of(forecasts, currency);
        assertEquals(THOSE_UNDER_IT,
                AStatementAtARow.readOf(often, forecasts, currency, Optional.empty()));
        assertEquals(AStatementAtARow.TurnsOn.OTHER_ELEMENTS,
                AStatementAtARow.readOf(often, forecasts, currency, Optional.of(ds)).turnsOn());
    }

    /** A number of one place is the element's, and reads the value where it is that place. */
    @Test
    void aNumberOfOnePlaceIsTheElements() {
        assertEquals(THE_ELEMENT, read(new NumericTerm.ValueOf(AMOUNT), CURRENCY));
        assertEquals(THE_ELEMENT, read(new NumericTerm.ValueOf(AMOUNT), null));
        assertEquals(new AStatementAtARow.WhatItReads(AStatementAtARow.TurnsOn.THE_ELEMENT, true),
                read(new NumericTerm.ValueOf(CURRENCY), CURRENCY));
    }

    /**
     * How often a value occurs, and what is gathered under it, turn on those holding the value
     * where the elements are grouped under it, and read only which elements those are — and turn
     * on others where the elements are grouped at another place, or each stands alone.
     */
    @Test
    void whatTheElementsOfAValueComeToTurnsOnThoseHoldingItAlone() {
        NumericTerm often = NumericTerm.Multiplicity.of(FS, CURRENCY);
        NumericTerm total = NumericTerm.GatheredUnderItsKey.of(FS.element(),
                new ElementKey.At(AT_THE_CURRENCY), THE_AMOUNT, Type.Prim.INT,
                NumericTerm.GatheredUnderItsKey.Gathering.TOTAL, null);
        NumericTerm least = NumericTerm.ExtremeOfItsKey.of(FS, CURRENCY, AMOUNT, Extreme.LEAST);
        NumericTerm kept = NumericTerm.OccurrencesOfItsValue.of(
                new RunSource.ProjectedOccurrences(CURRENCY), null);
        for (NumericTerm each : List.of(often, total, least, kept)) {
            assertEquals(THOSE_UNDER_IT, read(each, CURRENCY), each::toString);
            assertEquals(AStatementAtARow.TurnsOn.OTHER_ELEMENTS, read(each, AMOUNT).turnsOn(),
                    each::toString);
            assertEquals(AStatementAtARow.TurnsOn.OTHER_ELEMENTS, read(each, null).turnsOn(),
                    each::toString);
        }
    }

    /**
     * What a value's elements gather reads the value where it stands at the key: a total of the
     * currency's own number under the currency, or the least of it, is another number under each
     * currency, though the same elements hold it.
     */
    @Test
    void whatTheElementsGatherAtTheKeyReadsTheValue() {
        TermPath code = FS.element().then("code");
        ElementProjection atTheCode = ElementProjection.ofFields(List.of("code"));
        NumericTerm total = NumericTerm.GatheredUnderItsKey.of(FS.element(),
                new ElementKey.At(atTheCode), new ElementValue.Affine(LinearForm.atom(atTheCode)),
                Type.Prim.INT, NumericTerm.GatheredUnderItsKey.Gathering.TOTAL, null);
        NumericTerm least = NumericTerm.ExtremeOfItsKey.of(FS, code, code, Extreme.LEAST);
        for (NumericTerm each : List.of(total, least)) {
            assertEquals(new AStatementAtARow.WhatItReads(
                    AStatementAtARow.TurnsOn.THOSE_UNDER_ITS_VALUE, true), read(each, code),
                    each::toString);
        }
    }

    /**
     * A number of the elements a statement keeps reads what the statement does: kept by another
     * place of the element, it is still of those holding the value; kept by the value itself, a
     * group of them comes to another number under each value; kept by something of the container
     * as a whole, it turns on its other elements.
     */
    @Test
    void aNumberOfTheKeptElementsReadsWhatKeepsThem() {
        for (Function<KeptOccurrences, NumericTerm> of : List.<Function<KeptOccurrences,
                NumericTerm>>of(
                kept -> NumericTerm.OccurrencesOfItsValue.of(
                        new RunSource.ProjectedOccurrences(CURRENCY), kept),
                kept -> NumericTerm.GatheredUnderItsKey.of(FS.element(),
                        new ElementKey.At(AT_THE_CURRENCY), THE_AMOUNT, Type.Prim.INT,
                        NumericTerm.GatheredUnderItsKey.Gathering.TOTAL, kept))) {
            NumericTerm byTheAmount = of.apply(keptBy(AMOUNT));
            assertEquals(THOSE_UNDER_IT, read(byTheAmount, CURRENCY), byTheAmount::toString);
            NumericTerm byTheValue = of.apply(keptBy(CURRENCY));
            assertEquals(new AStatementAtARow.WhatItReads(
                    AStatementAtARow.TurnsOn.THOSE_UNDER_ITS_VALUE, true),
                    read(byTheValue, CURRENCY), byTheValue::toString);
            NumericTerm byTheContainer = of.apply(keptBy(FS));
            assertEquals(AStatementAtARow.TurnsOn.OTHER_ELEMENTS,
                    read(byTheContainer, CURRENCY).turnsOn(), byTheContainer::toString);
        }
    }

    /** The elements of {@code fs} kept where there is a value at {@code at}. */
    private static KeptOccurrences keptBy(TermPath at) {
        Proposition present = new Proposition.Present(new DecisionSubject.AnInput(at), true);
        return new KeptOccurrences(new DecisionSubject.AnInput(FS), present,
                AStatementAtARow.of(present, "f", null));
    }

    /** How often a value occurs in a container inside the element is the element's own. */
    @Test
    void howOftenAValueOccursInsideTheElementIsTheElements() {
        TermPath tags = FS.element().then("tags");
        assertEquals(THE_ELEMENT, read(NumericTerm.Multiplicity.of(tags, tags.element()),
                CURRENCY));
    }

    /**
     * A total of every element's amount turns on every other element, and one of another list's
     * on none of these.
     */
    @Test
    void aNumberTakenOverTheContainerTurnsOnItsOtherElements() {
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
        assertEquals(AStatementAtARow.TurnsOn.OTHER_ELEMENTS, read(overThese, CURRENCY).turnsOn());
        assertEquals(THE_ELEMENT, read(overOthers, CURRENCY));
    }
}
