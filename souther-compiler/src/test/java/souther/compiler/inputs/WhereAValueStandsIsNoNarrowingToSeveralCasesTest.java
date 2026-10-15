package souther.compiler.inputs;

import org.junit.jupiter.api.Test;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.ResolvedCase;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Where a value stands is a position, with every narrowing to several cases on the way to it taken
 * out, whichever of the three answers says so.
 *
 * <p>A narrowing to several cases is what a fork on the value reads; a reader asking where the
 * value stands is sent to the position, and a name read off such a value to that name at the sum.
 * An answer of several places is held to that at each of them, and stays an answer of several
 * places even where they come to one: what it says is that no read of the value is settled as one
 * place, which taking the narrowings out does not change.
 */
class WhereAValueStandsIsNoNarrowingToSeveralCasesTest {

    private static final TermPath KIND = TermPath.of("v").then("kind");

    private static final CasesLeft EITHER = CasesLeft.of(ResolvedCase.of(
            CaseSelector.direct(leaf("OnceKind")), List.of(leaf("Station"), leaf("Hospital"))));

    @Test
    void aPlaceUnderANarrowingToSeveralCasesIsTheNameAtTheSum() {
        PathResolution held = new PathResolution.At(KIND.refine(EITHER).then("items").element())
                .heldAt();
        assertEquals(new PathResolution.At(KIND.then("items").element()), held);
    }

    @Test
    void aNarrowingToOneCaseIsAPositionOfItsOwnAndStays() {
        TermPath station = KIND.refine(CasesLeft.of(Refinement.allOf(ResolvedCase.of(
                CaseSelector.direct(leaf("Station")), List.of(leaf("Station")))).getFirst()));
        assertEquals(new PathResolution.At(station.then("code")),
                new PathResolution.At(station.then("code")).heldAt());
    }

    @Test
    void eachPlaceAValueMayStandAtIsHeldTheSameWay() {
        TermPath other = TermPath.of("y").then("items").element();
        PathResolution held = new PathResolution.MayStandAt(List.of(
                KIND.refine(EITHER).then("items").element(), other)).heldAt();
        assertEquals(new PathResolution.MayStandAt(List.of(KIND.then("items").element(), other)),
                held);
    }

    @Test
    void severalPlacesThatComeToOneAreStillPlacesItMayStandAt() {
        TermPath named = KIND.then("items").element();
        PathResolution held = new PathResolution.MayStandAt(List.of(
                KIND.refine(EITHER).then("items").element(), named)).heldAt();
        assertEquals(new PathResolution.MayStandAt(List.of(named)), held);
    }

    private static TypeSymbol leaf(String name) {
        return TypeSymbols.declared(new TypeKey("m", name));
    }
}
