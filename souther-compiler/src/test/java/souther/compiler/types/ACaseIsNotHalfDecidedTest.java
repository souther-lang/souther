package souther.compiler.types;

import org.junit.jupiter.api.Test;
import souther.compiler.core.Core;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A resolved case says everything about itself, and the states that would say half of it are not
 * representable.
 *
 * <p>What a checker can produce is what a backend has to handle, so a state the backend has no
 * meaning for is one the checker must not be able to write. Three of them were reachable and are
 * not: a selector whose name and carrier disagree, a case whose held type disagrees with its name,
 * and an arm whose binding disagrees with what it selects. The first two are refused where the value
 * is made; the third is not refused but absent, the binding being read off the selection rather than
 * stored beside it.
 */
class ACaseIsNotHalfDecidedTest {

    private static final Type ELEMENT = Type.STRING;

    @Test
    void anOptionalsCarrierIsNamedByTheCaseItIs() {
        assertThrows(IllegalArgumentException.class,
                () -> new CaseSelector(TypeSymbol.SOME, new Refinement.OptionAbsent()),
                "`Some` carrying the absent carrier would be tested as absent and read as present");
        assertThrows(IllegalArgumentException.class,
                () -> new CaseSelector(TypeSymbol.NONE, new Refinement.OptionPresent(ELEMENT)),
                "`None` carrying the present one is the same mistake the other way round");
    }

    @Test
    void anOptionalsCaseIsOneOfItsOwnCarriers() {
        assertThrows(IllegalArgumentException.class,
                () -> CaseSelector.direct(TypeSymbol.SOME),
                "`Some` is a carrier of an optional, not a case whose class is the value");
    }

    @Test
    void theCarriersAnOptionalHasAreMadeWithTheirNames() {
        assertEquals(TypeSymbol.SOME, CaseSelector.optionPresent(ELEMENT).name());
        assertEquals(TypeSymbol.NONE, CaseSelector.optionAbsent().name());
        assertEquals(ELEMENT, CaseSelector.optionPresent(ELEMENT).bound());
        assertNull(CaseSelector.optionAbsent().bound(),
                "nothing readable stands under the absent carrier");
    }

    @Test
    void whatACaseHoldsComesFromItsName() {
        TypeSymbol anInt = TypeSymbol.primitive(Type.Prim.INT);
        assertEquals(Type.Prim.INT, CaseSelector.direct(anInt).bound(),
                "a case's name and what it holds are one fact, so a caller does not supply both");
        assertEquals(CaseSelector.heldBy(anInt), CaseSelector.direct(anInt).bound());
    }

    @Test
    void aCaseHoldsWhatItsNameHoldsHoweverItIsMade() {
        // The factory derives it; the constructor is a second way in and is held to the same thing,
        // or the rule would be one a caller can walk around by not using the factory.
        assertThrows(IllegalArgumentException.class,
                () -> new CaseSelector(TypeSymbol.primitive(Type.Prim.INT),
                        new Refinement.Direct(Type.BOOL)),
                "testing `Int`'s class and reading the value as `Bool` is not a case of anything");
    }

    @Test
    void anArmsBindingIsReadOffWhatItSelects() {
        CaseSelector present = CaseSelector.optionPresent(ELEMENT);
        assertEquals(present.refinement(), new Core.ResolvedPattern.Single(covering(present,
                        TypeSymbol.SOME)).binding(),
                "one case binds what that case's carrier holds, and there is nowhere to say"
                        + " otherwise");
        assertNull(new Core.ResolvedPattern.Single(
                        covering(CaseSelector.optionAbsent(), TypeSymbol.NONE)).bindType(),
                "a carrier holding nothing says so as fully as any other");
    }

    @Test
    void anArmAnsweringForSeveralBindsTheSubject() {
        TypeSymbol anInt = TypeSymbol.primitive(Type.Prim.INT);
        TypeSymbol aBool = TypeSymbol.primitive(Type.Prim.BOOL);
        Type subject = Type.union(java.util.Set.of(anInt, aBool));
        Core.ResolvedPattern.AnyOf several = new Core.ResolvedPattern.AnyOf(
                List.of(aLeaf(anInt), aLeaf(aBool)), subject);
        assertEquals(new Refinement.Direct(subject), several.binding(),
                "no one case type fits all of the alternatives, and each is already the subject");
    }

    @Test
    void anArmAnsweringForSeveralNamesSeveral() {
        TypeSymbol anInt = TypeSymbol.primitive(Type.Prim.INT);
        Type subject = Type.union(java.util.Set.of(anInt));
        assertThrows(IllegalArgumentException.class,
                () -> new Core.ResolvedPattern.AnyOf(List.of(aLeaf(anInt)), subject),
                "one case is a Single, which reads its binding off the case");
        assertThrows(IllegalArgumentException.class,
                () -> new Core.ResolvedPattern.AnyOf(List.of(), subject));
    }

    /** A leaf as this compile would resolve it: a case that covers itself. */
    private static ResolvedCase aLeaf(TypeSymbol leaf) {
        return covering(CaseSelector.direct(leaf), leaf);
    }

    private static ResolvedCase covering(CaseSelector selector, TypeSymbol... atoms) {
        return ResolvedCase.of(selector, List.of(atoms));
    }

    @Test
    void anArmSelectsSomething() {
        assertThrows(IllegalArgumentException.class,
                () -> new Core.ResolvedPattern.Single(null));
    }
}
