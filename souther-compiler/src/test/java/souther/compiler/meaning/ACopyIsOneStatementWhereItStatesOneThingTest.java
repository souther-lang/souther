package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.types.AnApplicationOfACall;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two identities, kept apart: what a site states, and how that was derived.
 *
 * <p>A site met twice is one statement where the two copies state one proposition, however each was
 * derived — so what is counted as stated does not split over a rule chosen differently. And what was
 * filed is equal to another filing only where the derivations are too, so a reader explaining a fork
 * from one is never handed the other's account.
 */
class ACopyIsOneStatementWhereItStatesOneThingTest {

    private static final MeaningsOfABody.Site SITE = new MeaningsOfABody.Site(
            new ModelOccurrence(new SourceConstructOrigin(new WrittenOwner.Body("m", "b"), 0, 0,
                    SourceConstruct.IF), ExpansionLineage.ORIGINAL),
            MeaningsOfABody.Part.Asked.CONDITION);

    private static final MeaningsOfABody.Site OTHER =
            new MeaningsOfABody.Site(SITE.construct(), MeaningsOfABody.Part.Asked.LEFT);

    private static final Derivation DIRECTLY =
            new Derivation.ATruthOfASubject(new DecisionSubject.AnInput(TermPath.of("flag")), true);

    private static final Derivation TWICE_DENIED = new Derivation.UnderADenial(
            new Derivation.UnderADenial(DIRECTLY, true), true);

    private static MeaningsOfABody.Meaning meaning(Derivation how) {
        return new Conclusion(Optional.empty()).meaningOf(how);
    }

    @Test
    void twoDerivationsOfOneThingAreOneStatement() {
        assertEquals(meaning(DIRECTLY).states(), meaning(TWICE_DENIED).states(),
                "the two derivations conclude one proposition");
        MeaningsOfABody.Filing filing = new MeaningsOfABody.Filing();
        filing.met(SITE, meaning(DIRECTLY));
        filing.met(SITE, meaning(TWICE_DENIED));
        MeaningsOfABody filed = filing.filed();
        assertFalse(filed.ambiguous().contains(SITE));
        assertEquals(Optional.of(meaning(DIRECTLY).states()), filed.at(SITE));
        assertEquals(DIRECTLY, filed.meaningAt(SITE).orElseThrow().how(),
                "the first derivation met is the one kept");
    }

    @Test
    void twoThingsStatedAtOneSiteAreAmbiguous() {
        MeaningsOfABody.Filing filing = new MeaningsOfABody.Filing();
        filing.met(SITE, meaning(DIRECTLY));
        filing.met(SITE, meaning(new Derivation.UnderADenial(DIRECTLY, true)));
        filing.met(SITE, meaning(DIRECTLY));
        MeaningsOfABody filed = filing.filed();
        assertTrue(filed.ambiguous().contains(SITE));
        assertEquals(Optional.empty(), filed.at(SITE));
        assertFalse(filed.stated().containsKey(SITE),
                "a site stating two things holds neither, and stays so whatever is met after");
    }

    /** What each application states is kept under it, beside what the site states on some
     *  application, and an application not told apart is kept under none. */
    @Test
    void eachApplicationToldApartIsKeptUnderItself() {
        MeaningsOfABody.Filing filing = new MeaningsOfABody.Filing();
        filing.metOnEachApplication(List.of(
                new MeaningsOfABody.ReadOnAnApplication(Optional.of(application(0)),
                        reading(meaning(DIRECTLY))),
                new MeaningsOfABody.ReadOnAnApplication(Optional.of(application(1)),
                        reading(meaning(new Derivation.UnderADenial(DIRECTLY, true)))),
                new MeaningsOfABody.ReadOnAnApplication(Optional.empty(),
                        reading(meaning(DIRECTLY)))));
        MeaningsOfABody filed = filing.filed();
        assertTrue(filed.at(SITE).orElseThrow() instanceof Proposition.OnAnApplication);
        assertEquals(Optional.of(meaning(DIRECTLY).states()),
                filed.onTheApplication(application(0)).orElseThrow().at(SITE));
        assertEquals(Optional.of(meaning(DIRECTLY).states().denied()),
                filed.onTheApplication(application(1)).orElseThrow().at(SITE));
        assertEquals(Set.of(application(0), application(1)), filed.applications().keySet());
    }

    /**
     * One application met again is filed as a site met again is: one proposition derived two ways
     * is one statement there, with the first derivation kept.
     */
    @Test
    void anApplicationMetAgainStatingOneThingAnotherWayIsOneStatement() {
        MeaningsOfABody.Filing filing = new MeaningsOfABody.Filing();
        filing.metOnEachApplication(List.of(new MeaningsOfABody.ReadOnAnApplication(
                Optional.of(application(0)), reading(Map.of(SITE, meaning(DIRECTLY))))));
        filing.metOnEachApplication(List.of(new MeaningsOfABody.ReadOnAnApplication(
                Optional.of(application(0)), reading(Map.of(SITE, meaning(TWICE_DENIED))))));
        MeaningsOfABody onIt = filing.filed().onTheApplication(application(0)).orElseThrow();
        assertEquals(Optional.of(meaning(DIRECTLY).states()), onIt.at(SITE));
        assertEquals(DIRECTLY, onIt.meaningAt(SITE).orElseThrow().how());
    }

    /**
     * And met again stating something else at a site, that site says nothing on the application,
     * as a site whose copies differ says nothing; what the application states elsewhere stands.
     */
    @Test
    void anApplicationMetAgainStatingAnotherThingAtASiteSaysNothingThereAlone() {
        MeaningsOfABody.Filing filing = new MeaningsOfABody.Filing();
        filing.metOnEachApplication(List.of(new MeaningsOfABody.ReadOnAnApplication(
                Optional.of(application(0)),
                reading(Map.of(SITE, meaning(DIRECTLY), OTHER, meaning(DIRECTLY))))));
        filing.metOnEachApplication(List.of(new MeaningsOfABody.ReadOnAnApplication(
                Optional.of(application(0)), reading(Map.of(SITE,
                        meaning(new Derivation.UnderADenial(DIRECTLY, true)))))));
        MeaningsOfABody onIt = filing.filed().onTheApplication(application(0)).orElseThrow();
        assertEquals(Optional.empty(), onIt.at(SITE));
        assertEquals(new WhyUnread.CopiesStateDifferentThings(), onIt.whyNothingAt(SITE));
        assertEquals(Optional.of(meaning(DIRECTLY).states()), onIt.at(OTHER));
    }

    /** What a reading told ambiguous stays so, and what it filed under an application is filed
     *  under that application, wherever it is taken in. */
    @Test
    void aReadingTakenInWholeKeepsWhatItFoundAmbiguousAndWhatItStatesOnEachApplication() {
        MeaningsOfABody.Filing inside = new MeaningsOfABody.Filing();
        inside.met(SITE, meaning(DIRECTLY));
        inside.met(SITE, meaning(new Derivation.UnderADenial(DIRECTLY, true)));
        inside.metOnEachApplication(List.of(new MeaningsOfABody.ReadOnAnApplication(
                Optional.of(application(0)), reading(Map.of(OTHER, meaning(DIRECTLY))))));
        MeaningsOfABody.Filing outside = new MeaningsOfABody.Filing();
        outside.metAll(inside.filed());
        outside.met(SITE, meaning(DIRECTLY));
        MeaningsOfABody filed = outside.filed();
        assertEquals(Optional.empty(), filed.at(SITE));
        assertEquals(Optional.of(meaning(DIRECTLY).states()),
                filed.onTheApplication(application(0)).orElseThrow().at(OTHER));
    }

    /** A site is not both stated and ambiguous, however the value is made. */
    @Test
    void aSiteIsNotFiledAsBothStatedAndAmbiguous() {
        assertThrows(IllegalArgumentException.class, () -> new MeaningsOfABody(
                Map.of(SITE, meaning(DIRECTLY)), Set.of(SITE), Set.of(), Map.of()));
    }

    private static AnApplicationOfACall application(int ordinal) {
        return new AnApplicationOfACall(new ModelOccurrence(new SourceConstructOrigin(
                new WrittenOwner.Body("m", "b"), 1, 0, SourceConstruct.CALL),
                ExpansionLineage.ORIGINAL), ordinal);
    }

    /** A reading of a body that states {@code meaning} at the site and nothing else. */
    private static MeaningsOfABody reading(MeaningsOfABody.Meaning meaning) {
        return reading(Map.of(SITE, meaning));
    }

    /** A reading of a body that states each of {@code stated} at its site. */
    private static MeaningsOfABody reading(
            Map<MeaningsOfABody.Site, MeaningsOfABody.Meaning> stated) {
        MeaningsOfABody.Filing filing = new MeaningsOfABody.Filing();
        stated.forEach(filing::met);
        return filing.filed();
    }

    @Test
    void whatWasFiledIsEqualOnlyWhereHowItWasDerivedIsToo() {
        MeaningsOfABody.Filing one = new MeaningsOfABody.Filing();
        one.met(SITE, meaning(DIRECTLY));
        MeaningsOfABody.Filing other = new MeaningsOfABody.Filing();
        other.met(SITE, meaning(TWICE_DENIED));
        assertEquals(one.filed().at(SITE), other.filed().at(SITE));
        assertNotEquals(one.filed(), other.filed());
    }
}
