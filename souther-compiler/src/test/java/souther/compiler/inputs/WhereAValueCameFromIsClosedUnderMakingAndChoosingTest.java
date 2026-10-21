package souther.compiler.inputs;

import org.junit.jupiter.api.Test;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.ResolvedCase;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Where a value came from is an answer that can be made of several places together and chosen
 * between, and each of those operations takes what the other gave.
 *
 * <p>A value a fold made from a seed and a list is made of both; a value an {@code if} chose
 * between two of those is one or the other of them, each made of two; a fold seeded with such a
 * value is made of that and of its own list. None of those may drop a place on the way, since a
 * rule about the value is filed at the places it came from and a place dropped is a rule nobody is
 * told is unread.
 */
class WhereAValueCameFromIsClosedUnderMakingAndChoosingTest {

    private static final TermPath A = TermPath.of("a").then("items").element();
    private static final TermPath B = TermPath.of("b").then("items").element();
    private static final TermPath C = TermPath.of("c").then("items").element();
    private static final TermPath D = TermPath.of("d").then("items").element();

    private static PathResolution at(TermPath path) {
        return new PathResolution.At(path);
    }

    /** Made of every one of {@code places} together. */
    private static PathResolution together(TermPath... places) {
        return new PathResolution.MadeOf(List.of(List.of(places)));
    }

    /** Made of the one pair together or of the other. */
    private static PathResolution eitherPair(TermPath first, TermPath second, TermPath third,
                                             TermPath fourth) {
        return new PathResolution.MadeOf(List.of(List.of(first, second), List.of(third, fourth)));
    }

    @Test
    void aChoiceBetweenTwoValuesMadeOfSeveralKeepsEveryPlaceOfBoth() {
        PathResolution chosen = PathResolution.anyOf(List.of(
                PathResolution.madeOf(List.of(at(A), at(B))),
                PathResolution.madeOf(List.of(at(C), at(D)))));
        assertEquals(eitherPair(A, B, C, D), chosen);
    }

    @Test
    void aValueMadeOfOneOfTwoPlacesAndAnotherIsMadeOfEachPairInTurn() {
        PathResolution chosen = new PathResolution.MayStandAt(List.of(B, C));
        assertEquals(eitherPair(A, B, A, C),
                PathResolution.madeOf(List.of(at(A), chosen)));
    }

    @Test
    void aValueMadeOfAValueMadeOfSeveralIsMadeOfAllOfThem() {
        assertEquals(together(A, B, C), PathResolution.madeOf(List.of(
                PathResolution.madeOf(List.of(at(A), at(B))), at(C))));
    }

    @Test
    void aPartThatCameFromNowhereTheInputHoldsAddsNoPlace() {
        assertEquals(at(A), PathResolution.madeOf(List.of(
                at(A), new PathResolution.NotAPosition())));
        assertEquals(together(A, B), PathResolution.madeOf(List.of(
                new PathResolution.NotAPosition(), at(A), at(B))));
    }

    @Test
    void aValueEveryPartOfWhichCameFromNowhereHasNoPlaceToName() {
        assertEquals(new PathResolution.NotAPosition(), PathResolution.madeOf(List.of(
                new PathResolution.NotAPosition(), new PathResolution.NotAPosition())));
        assertEquals(new PathResolution.NotAPosition(), PathResolution.madeOf(List.of()));
    }

    @Test
    void aChoiceWhereOneCaseCameFromNowhereKeepsTheOnesThatDidNot() {
        assertEquals(together(A, B), PathResolution.anyOf(List.of(
                PathResolution.madeOf(List.of(at(A), at(B))), new PathResolution.NotAPosition())));
    }

    @Test
    void placesThatComeToOneWhereTheNarrowingsAreTakenOutAreThatOnePlace() {
        CasesLeft either = CasesLeft.of(ResolvedCase.of(
                CaseSelector.direct(leaf("OnceKind")), List.of(leaf("Station"), leaf("Hospital"))));
        TermPath narrowed = A.refine(either);
        assertEquals(at(A), together(narrowed, A).heldAt());
        assertEquals(together(A, B), together(narrowed, B).heldAt());
    }

    @Test
    void anElementOfWhatIsMadeOfSeveralContainersIsMadeOfAnElementOfEach() {
        assertEquals(together(A.then("x"), B.then("x")),
                together(A, B).deeper(path -> path.then("x")));
    }

    @Test
    void aFieldOfAValueMadeOfSeveralPlacesIsMadeOfThosePlacesAndNotOfAFieldOfEach() {
        PathResolution made = together(A, B);
        assertEquals(made, made.throughAField(path -> path.then("count")));
        assertEquals(at(A.then("count")), at(A).throughAField(path -> path.then("count")));
    }

    /** One part of {@code ways} places it may stand at, named {@code name} and a number. */
    private static PathResolution mayStandAtOneOf(String name, int ways) {
        List<TermPath> among = new ArrayList<>();
        for (int i = 0; i < ways; i++) {
            among.add(TermPath.of(name + i).then("items").element());
        }
        return new PathResolution.MayStandAt(among);
    }

    @Test
    void aValueMadeInAsManyWaysAsAnAnswerTellsApartKeepsEveryWay() {
        PathResolution.MadeOf made = (PathResolution.MadeOf) PathResolution.madeOf(List.of(
                mayStandAtOneOf("p", 4), mayStandAtOneOf("q", 4), mayStandAtOneOf("r", 4)));
        assertEquals(PathResolution.MOST_WAYS_TOLD_APART, made.alternatives().size());
        assertEquals(true, made.alternatives().stream().allMatch(each -> each.size() == 3));
    }

    @Test
    void aValueMadeInMoreWaysThanThatIsMadeOfAllTheirPlacesTogether() {
        PathResolution first = mayStandAtOneOf("p", 8);
        PathResolution second = mayStandAtOneOf("q", 9);
        PathResolution.MadeOf made = (PathResolution.MadeOf) PathResolution.madeOf(
                List.of(first, second));
        assertEquals(1, made.alternatives().size());
        List<TermPath> every = new ArrayList<>(((PathResolution.MayStandAt) first).among());
        every.addAll(((PathResolution.MayStandAt) second).among());
        assertEquals(Set.copyOf(every), Set.copyOf(made.alternatives().getFirst()));
    }

    private static TypeSymbol leaf(String name) {
        return TypeSymbols.declared(new TypeKey("m", name));
    }
}
