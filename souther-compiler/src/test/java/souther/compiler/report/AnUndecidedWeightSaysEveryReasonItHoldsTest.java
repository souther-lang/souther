package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.check.Carrier;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.partition.BorderQuantity;
import souther.compiler.partition.LinearQuantity;
import souther.compiler.publish.PublicationOrders;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OneBorder;
import souther.compiler.query.TiltOfADerivedValue;
import souther.compiler.query.TiltOfADerivedValue.Standing;
import souther.compiler.query.Weakening;
import souther.compiler.query.Weakening.AWeightNotDecided.Why;
import souther.compiler.query.WeakeningSet;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A weight the rows leave undecided says each thing it went without, whichever of them there are.
 *
 * <p>{@code Standing.Undecided} holds the weight's own reasons and what the borders of the
 * computation went without, and a weight may hold either or both. These are asked of the page
 * written for each of the states, with positions weighed into more than one form: states a real
 * model reaches only by accident, and which a page that said one of the two would hide.
 */
class AnUndecidedWeightSaysEveryReasonItHoldsTest {

    private static final NumericTerm A = new NumericTerm.ValueOf(TermPath.of("a"));
    private static final NumericTerm B = new NumericTerm.ValueOf(TermPath.of("b"));
    private static final NumericTerm C = new NumericTerm.ValueOf(TermPath.of("c"));

    private static final Standing OWN_ONLY = new Standing.Undecided(WeakeningSet.none(),
            PublicationOrders.WEIGHT_NOT_DECIDED_REASONS.keep(Set.of(Why.A_BORDER_WAS_NOT_READ_IN_FULL)));

    private static final Standing CARRIED_ONLY = new Standing.Undecided(
            WeakeningSet.of(new Weakening.BodyNotInEvaluation("b")),
            PublicationOrders.WEIGHT_NOT_DECIDED_REASONS.keep(Set.of()));

    private static final Standing BOTH = new Standing.Undecided(
            WeakeningSet.of(new Weakening.BodyNotInEvaluation("b")),
            PublicationOrders.WEIGHT_NOT_DECIDED_REASONS.keep(Set.of(Why.A_RUN_WAS_NOT_WATCHED)));

    private static final Compilation ANY = ACompiledModel.measured("""
            module m
            data Yes
            behavior f : (x: Int) -> Yes
            let f (x) = Yes
            """, Adequacy.Asked.fullReport());

    private static LinearQuantity form(NumericTerm first, NumericTerm second) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(first, ExactRatio.ONE);
        coefs.put(second, ExactRatio.ONE);
        Map<NumericTerm, TermOrders> on = new LinkedHashMap<>();
        on.put(first, TermOrdersFixtures.itself(first, Carrier.WHOLE));
        on.put(second, TermOrdersFixtures.itself(second, Carrier.WHOLE));
        return new BorderQuantity.OverAForm("b", new LinearForm<>(ExactRatio.ZERO, coefs), on);
    }

    /** The computation's weights, each position standing as it is given, in the forms given. */
    private static String said(Map<NumericTerm, Standing> positions, LinearQuantity... forms) {
        TiltOfADerivedValue tilt = new TiltOfADerivedValue(OneBorder.derivedValue(),
                new LinkedHashMap<>(positions), List.of(forms), List.of());
        StringBuilder out = new StringBuilder();
        AdequacyReport.weightsNotDecided(out, List.of(tilt),
                new Page(SourceRendering.namedByIdentity(ANY.texts()), Locale.ENGLISH));
        return out.toString();
    }

    @Test
    void aWeightUndecidedOnlyForItsOwnReasonSaysThatReasonAndNothingOfItsBorders() {
        String page = said(Map.of(A, OWN_ONLY), form(A, B));

        assertTrue(page.contains("because a border of it was not read in full"), page);
        assertFalse(page.contains("its borders went without"), page);
    }

    @Test
    void aWeightUndecidedOnlyByWhatItsBordersWentWithoutSaysThemAndNoOwnReason() {
        String page = said(Map.of(A, CARRIED_ONLY), form(A, B));

        assertTrue(page.contains("its borders went without: body_not_in_evaluation"), page);
        assertFalse(page.contains("because a border"), page);
        assertFalse(page.contains("because no border"), page);
        assertTrue(page.contains("· a"), page);
    }

    @Test
    void aWeightUndecidedForBothSaysEachOnItsOwnLine() {
        String page = said(Map.of(A, BOTH), form(A, B));

        assertTrue(page.contains("because a row was left out because nothing watched its run"),
                page);
        assertTrue(page.contains("its borders went without: body_not_in_evaluation"), page);
    }

    /** Positions weighed into different forms are not one group however alike their reasons read,
     *  and neither are two that went without different things. */
    @Test
    void positionsInDifferentFormsAndWithDifferentReasonsAreDifferentEntries() {
        Map<NumericTerm, Standing> positions = new LinkedHashMap<>();
        positions.put(A, OWN_ONLY);
        positions.put(C, OWN_ONLY);
        String together = said(positions, form(A, B), form(B, C));
        assertEquals(2, together.lines().filter(each -> each.contains("? not decided")).count(),
                together);

        Map<NumericTerm, Standing> apart = new LinkedHashMap<>();
        apart.put(A, OWN_ONLY);
        apart.put(B, CARRIED_ONLY);
        String reasons = said(apart, form(A, B));
        assertEquals(2, reasons.lines().filter(each -> each.contains("? not decided")).count(),
                reasons);
    }
}
