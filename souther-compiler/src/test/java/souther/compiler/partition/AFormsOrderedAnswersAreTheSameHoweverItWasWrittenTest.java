package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a reader answers about a form in an order is the same for both writings of one form.
 *
 * <p>A form is a mapping from terms to coefficients. {@code 6 * b + 3 * a} and {@code 3 * a + 6 * b}
 * are one form and the mapping says so, and neither the mapping nor anything comparing two of them
 * can see which term was written first. A reader that takes the terms off the mapping reads that
 * order anyway — so two readers of one form disagree about which term comes first, and one reader
 * disagrees with itself after a rewrite that changed nothing.
 *
 * <p>Which is why the order a form is walked in is what its terms are called
 * ({@link souther.compiler.inputs.NumericTerms}), and the readers whose answers have an order in
 * them ask for it there. That the one order exists is held where it is written; what is held here
 * is that these readers go through it, which is the half a contract on the order cannot state.
 *
 * <p>The readers are the ones whose answer is a sequence or a text: where a reading files what it
 * found, what a quantity's terms are, and how a report spells a direction. A reader whose answer is
 * a sum, a set or a condition of every term comes to the same thing whichever way the walk went and
 * is not one of these.
 */
class AFormsOrderedAnswersAreTheSameHoweverItWasWrittenTest {

    private static final NumericTerm FIRST_WRITTEN = at("b");

    private static final NumericTerm SECOND_WRITTEN = at("a");

    private static NumericTerm at(String head) {
        return new NumericTerm.ValueOf(TermPath.of(head));
    }

    /** The same form each time: what stands at a term goes with the term and not with where it was
     *  written. What the arguments settle is the order the two were put in. */
    private static Map<NumericTerm, ExactRatio> written(NumericTerm one, NumericTerm other) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(one, coefficientAt(one));
        coefs.put(other, coefficientAt(other));
        return coefs;
    }

    private static ExactRatio coefficientAt(NumericTerm term) {
        return ExactRatio.of(term.equals(FIRST_WRITTEN) ? 6 : 3);
    }

    private static LinearForm<NumericTerm> form(NumericTerm one, NumericTerm other) {
        return new LinearForm<>(ExactRatio.ZERO, written(one, other));
    }

    /**
     * And the two writings are two, which is what makes the rest of this a question.
     *
     * <p>Two mappings filled in one order would come out alike whatever a reader did with them, and
     * every answer below would hold while saying nothing.
     */
    @Test
    void theTwoWritingsAreTwo() {
        Map<NumericTerm, ExactRatio> oneWay = written(FIRST_WRITTEN, SECOND_WRITTEN);
        Map<NumericTerm, ExactRatio> theOther = written(SECOND_WRITTEN, FIRST_WRITTEN);

        assertEquals(oneWay, theOther, "the two hold the same coefficients at the same terms");
        assertTrue(!List.copyOf(oneWay.keySet()).equals(List.copyOf(theOther.keySet())),
                "and hand their terms over in different orders");
    }

    /** What a form comes to when it is ordered is what its terms are called, either way round. */
    @Test
    void whatAFormComesToWhenItIsOrderedIsTheSameEitherWay() {
        assertEquals(AffineReading.ordered(form(FIRST_WRITTEN, SECOND_WRITTEN)),
                AffineReading.ordered(form(SECOND_WRITTEN, FIRST_WRITTEN)));
        assertEquals(List.of(Map.entry(SECOND_WRITTEN, ExactRatio.of(3)),
                        Map.entry(FIRST_WRITTEN, ExactRatio.of(6))),
                AffineReading.ordered(form(FIRST_WRITTEN, SECOND_WRITTEN)),
                "which is the order of what each term is called");
    }

    /** And where a reading files what it found is the same either way. */
    @Test
    void andWhereAReadingFilesWhatItFoundIsTheSameEitherWay() {
        assertEquals(AffineReading.filedAt(met(FIRST_WRITTEN, SECOND_WRITTEN)),
                AffineReading.filedAt(met(SECOND_WRITTEN, FIRST_WRITTEN)));
        assertEquals(List.of(FilingCoordinate.of(SECOND_WRITTEN), FilingCoordinate.of(FIRST_WRITTEN)),
                AffineReading.filedAt(met(FIRST_WRITTEN, SECOND_WRITTEN)));
    }

    /** And a quantity's terms are the same either way. */
    @Test
    void andAQuantitysTermsAreTheSameEitherWay() {
        assertEquals(quantityOver(FIRST_WRITTEN, SECOND_WRITTEN).terms(),
                quantityOver(SECOND_WRITTEN, FIRST_WRITTEN).terms());
        assertEquals(List.of(SECOND_WRITTEN, FIRST_WRITTEN),
                quantityOver(FIRST_WRITTEN, SECOND_WRITTEN).terms());
    }

    /** And what a report spells a direction as is the same either way. */
    @Test
    void andWhatAReportSpellsADirectionAsIsTheSameEitherWay() {
        String spelled = OrderedAffineBoundary.spelled(written(FIRST_WRITTEN, SECOND_WRITTEN));

        assertEquals(spelled, OrderedAffineBoundary.spelled(written(SECOND_WRITTEN, FIRST_WRITTEN)));
        assertTrue(spelled.indexOf("a") < spelled.indexOf("b"),
                "and names the terms in the order they are called: " + spelled);
    }

    /** The terms a reading met, in the order the argument settles. */
    private static Set<NumericTerm> met(NumericTerm one, NumericTerm other) {
        Set<NumericTerm> terms = new LinkedHashSet<>();
        terms.add(one);
        terms.add(other);
        return terms;
    }

    private static BorderQuantity.OverAForm quantityOver(NumericTerm one, NumericTerm other) {
        Map<NumericTerm, TermOrders> on = new LinkedHashMap<>();
        on.put(one, TermOrdersFixtures.itself(one, Carrier.WHOLE));
        on.put(other, TermOrdersFixtures.itself(other, Carrier.WHOLE));
        return new BorderQuantity.OverAForm("decide", form(one, other), on);
    }
}
