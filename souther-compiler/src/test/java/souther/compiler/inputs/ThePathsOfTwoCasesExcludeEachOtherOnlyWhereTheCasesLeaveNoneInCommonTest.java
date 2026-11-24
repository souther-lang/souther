package souther.compiler.inputs;

import org.junit.jupiter.api.Test;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.ResolvedCase;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two paths exclude each other's cases where the cases each requires of a value leave it none in
 * common, and not where they are only paths to places apart: a row where an element is in one case
 * of a sum says nothing of whether it is in a case of a sum beside it, so a place read under the
 * one is still read there.
 */
class ThePathsOfTwoCasesExcludeEachOtherOnlyWhereTheCasesLeaveNoneInCommonTest {

    private static final TermPath REACH = TermPath.of("c").then("reach");
    private static final TermPath STATUS = TermPath.of("c").then("status");

    private static final TypeSymbol EMAIL_ONLY = leaf("EmailOnly");
    private static final TypeSymbol PHONE_ONLY = leaf("PhoneOnly");
    private static final TypeSymbol ACTIVE = leaf("Active");

    @Test
    void twoCasesOfOneSumExcludeEachOther() {
        TermPath phone = REACH.refine(only(PHONE_ONLY));
        TermPath email = REACH.refine(only(EMAIL_ONLY)).then("email");

        assertTrue(phone.excludesTheCasesOf(email));
        assertTrue(email.excludesTheCasesOf(phone));
    }

    @Test
    void aCaseOfOneSumAndAPlaceUnderAnotherSumAreApartButExcludeNothing() {
        TermPath active = STATUS.refine(only(ACTIVE));
        TermPath email = REACH.refine(only(EMAIL_ONLY)).then("email");

        assertFalse(active.bearsOn(email), "the two are shown apart");
        assertFalse(active.excludesTheCasesOf(email));
        assertFalse(email.excludesTheCasesOf(active));
    }

    @Test
    void theSameCaseExcludesNothingOfItself() {
        TermPath email = REACH.refine(only(EMAIL_ONLY)).then("email");

        assertFalse(email.excludesTheCasesOf(email));
        assertFalse(REACH.refine(only(EMAIL_ONLY)).excludesTheCasesOf(email));
    }

    private static CasesLeft only(TypeSymbol leaf) {
        return CasesLeft.of(ResolvedCase.of(CaseSelector.direct(leaf), List.of(leaf)));
    }

    private static TypeSymbol leaf(String name) {
        return TypeSymbols.declared(new TypeKey("m", name));
    }
}
