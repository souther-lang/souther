package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.ElementKey;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.LinearForm;
import souther.compiler.query.Compilation;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What an element's answer turns on, among the elements of a container held as groups under one
 * value, is read off each number the answer reads by the container that number is read among
 * ({@link AStatementAtARow#turnsOn}). A container is chosen by what a row holding one group alone
 * answers only where nothing turns on more than the group.
 */
class WhatAnElementsAnswerTurnsOnIsReadOffEachNumberTest {

    private static final TermPath FS = TermPath.of("fs");

    private static final TermPath CURRENCY = FS.element().then("currency");

    private static final TermPath AMOUNT = FS.element().then("amount");

    private static final ElementProjection AT_THE_CURRENCY =
            ElementProjection.ofFields(List.of("currency"));

    private static final ElementValue THE_AMOUNT =
            new ElementValue.Affine(LinearForm.atom(ElementProjection.ofFields(List.of("amount"))));

    /** A number of one place is the element's, whichever place the elements are grouped at. */
    @Test
    void aNumberOfOnePlaceIsTheElements() {
        assertEquals(AStatementAtARow.TurnsOn.THE_ELEMENT,
                AStatementAtARow.turnsOn(new NumericTerm.ValueOf(AMOUNT), FS, CURRENCY));
        assertEquals(AStatementAtARow.TurnsOn.THE_ELEMENT,
                AStatementAtARow.turnsOn(new NumericTerm.ValueOf(AMOUNT), FS, null));
    }

    /**
     * How often a value occurs, and what is gathered under it, turn on those holding the value
     * where the elements are grouped under it — and on others where they are grouped at another
     * place, or each element stands alone.
     */
    @Test
    void whatTheElementsOfAValueComeToTurnsOnThoseHoldingItAlone() {
        NumericTerm often = NumericTerm.Multiplicity.of(FS, CURRENCY);
        NumericTerm total = NumericTerm.GatheredUnderItsKey.of(FS.element(),
                new ElementKey.At(AT_THE_CURRENCY), THE_AMOUNT, Type.Prim.INT,
                NumericTerm.GatheredUnderItsKey.Gathering.TOTAL, null);
        NumericTerm kept = NumericTerm.OccurrencesOfItsValue.of(
                new RunSource.ProjectedOccurrences(CURRENCY), null);
        for (NumericTerm each : List.of(often, total, kept)) {
            assertEquals(AStatementAtARow.TurnsOn.THOSE_UNDER_ITS_VALUE,
                    AStatementAtARow.turnsOn(each, FS, CURRENCY), each::toString);
            assertEquals(AStatementAtARow.TurnsOn.OTHER_ELEMENTS,
                    AStatementAtARow.turnsOn(each, FS, AMOUNT), each::toString);
            assertEquals(AStatementAtARow.TurnsOn.OTHER_ELEMENTS,
                    AStatementAtARow.turnsOn(each, FS, null), each::toString);
        }
    }

    /** How often a value occurs in a container inside the element is the element's own. */
    @Test
    void howOftenAValueOccursInsideTheElementIsTheElements() {
        TermPath tags = FS.element().then("tags");
        assertEquals(AStatementAtARow.TurnsOn.THE_ELEMENT, AStatementAtARow.turnsOn(
                NumericTerm.Multiplicity.of(tags, tags.element()), FS, CURRENCY));
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
        assertEquals(AStatementAtARow.TurnsOn.OTHER_ELEMENTS,
                AStatementAtARow.turnsOn(overThese, FS, CURRENCY));
        assertEquals(AStatementAtARow.TurnsOn.THE_ELEMENT,
                AStatementAtARow.turnsOn(overOthers, FS, CURRENCY));
    }
}
