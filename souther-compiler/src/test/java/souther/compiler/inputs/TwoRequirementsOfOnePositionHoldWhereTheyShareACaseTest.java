package souther.compiler.inputs;

import org.junit.jupiter.api.Test;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.ResolvedCase;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * Two requirements of one position hold together exactly where they leave it a case in common, and
 * what holds is the cases both leave.
 *
 * <p>The one compatibility rule, asked by every reader that decides whether two positions, two
 * classes or two conditions can be in one row. Equality is the case of one case on each side:
 * {@code Station} against {@code Hospital} is a conflict, and {@code Station or Hospital} against
 * {@code Station} is a {@code Station}.
 */
class TwoRequirementsOfOnePositionHoldWhereTheyShareACaseTest {

    private static final TermPath KIND = TermPath.of("v").then("kind");

    private static final TypeSymbol STATION = leaf("Station");
    private static final TypeSymbol HOSPITAL = leaf("Hospital");

    @Test
    void aNarrowingToSeveralCasesAndOneOfThemIsThatOne() {
        Requirements merged = assertInstanceOf(Requirements.Merge.Merged.class,
                at(either()).merge(at(only(STATION)))).requirements();
        assertEquals(only(STATION), merged.at(KIND));
        assertEquals(merged.refinements(), assertInstanceOf(Requirements.Merge.Merged.class,
                        at(only(STATION)).merge(at(either()))).requirements().refinements(),
                "and the same whichever is said first");
    }

    @Test
    void twoCasesWithNothingInCommonAreAConflict() {
        Requirements.Merge.Conflict conflict = assertInstanceOf(Requirements.Merge.Conflict.class,
                at(only(STATION)).merge(at(only(HOSPITAL))));
        assertEquals(KIND, conflict.at());
    }

    @Test
    void theSameCasesHoldTogetherAsThemselves() {
        assertEquals(either(), assertInstanceOf(Requirements.Merge.Merged.class,
                at(either()).merge(at(either()))).requirements().at(KIND));
    }

    /**
     * One case is spelled as that case, and several are spelled in one order whatever
     * order they were met in, so that one set is one position.
     */
    @Test
    void oneCaseKeepsItsSpellingAndSeveralAreSpelledInOneOrder() {
        assertEquals("v.kind@Station", KIND.refine(only(STATION)).toString());
        CasesLeft hospitalFirst = CasesLeft.of(ResolvedCase.of(
                CaseSelector.direct(leaf("OnceKind")), List.of(HOSPITAL, STATION)));
        CasesLeft stationFirst = CasesLeft.of(ResolvedCase.of(
                CaseSelector.direct(leaf("OnceKind")), List.of(STATION, HOSPITAL)));
        assertEquals(hospitalFirst, stationFirst);
        assertEquals("v.kind@{Hospital|Station}", KIND.refine(stationFirst).toString());
        assertNotEquals(KIND.refine(stationFirst), KIND.refine(only(STATION)));
    }

    private static Requirements at(CasesLeft cases) {
        return Requirements.NONE.and(KIND, cases);
    }

    private static CasesLeft either() {
        return CasesLeft.of(ResolvedCase.of(CaseSelector.direct(leaf("OnceKind")),
                List.of(STATION, HOSPITAL)));
    }

    private static CasesLeft only(TypeSymbol leaf) {
        return CasesLeft.of(ResolvedCase.of(CaseSelector.direct(leaf), List.of(leaf)));
    }

    private static TypeSymbol leaf(String name) {
        return TypeSymbols.declared(new TypeKey("m", name));
    }
}
