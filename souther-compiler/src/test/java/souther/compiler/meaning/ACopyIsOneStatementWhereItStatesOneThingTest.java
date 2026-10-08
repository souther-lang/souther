package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
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
            MeaningsOfABody.Part.CONDITION);

    private static final Derivation DIRECTLY =
            new Derivation.ATruthAtAPosition(TermPath.of("flag"), true);

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
        MeaningsOfABody filed = filing.filed();
        assertTrue(filed.ambiguous().contains(SITE));
        assertEquals(Optional.empty(), filed.at(SITE));
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
