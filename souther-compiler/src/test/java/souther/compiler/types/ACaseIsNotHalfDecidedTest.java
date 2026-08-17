package souther.compiler.types;

import org.junit.jupiter.api.Test;
import souther.compiler.core.Core;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A resolved case says everything about itself, and the states that would say half of it are not
 * representable.
 *
 * <p>Two of them. A selector's name and its carrier are one decision written twice, and a selector
 * spelled {@code Some} whose carrier were the absent one would be tested as absent and reported as
 * present, with nothing to say which half was the mistake. And an arm binds what its carrier holds,
 * which a carrier holding nothing says as fully as any other — so there is no arm that binds
 * nothing, and no null standing for one.
 *
 * <p>Both are refused where the value is made rather than checked by whoever reads it. What a
 * checker could produce is what a backend has to handle, so a state the backend has no meaning for
 * is one the checker must not be able to write.
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
                () -> CaseSelector.direct(TypeSymbol.SOME, ELEMENT),
                "`Some` is a carrier of an optional, not a case whose class is the value");
    }

    @Test
    void theCarriersAnOptionalHasAreMadeWithTheirNames() {
        assertEquals(TypeSymbol.SOME, CaseSelector.optionPresent(ELEMENT).name());
        assertEquals(TypeSymbol.NONE, CaseSelector.optionAbsent().name());
        assertEquals(ELEMENT, CaseSelector.optionPresent(ELEMENT).bound());
        assertEquals(null, CaseSelector.optionAbsent().bound(),
                "nothing readable stands under the absent carrier");
    }

    @Test
    void anArmBindsWhatItsCarrierHolds() {
        List<CaseSelector> one = List.of(CaseSelector.optionAbsent());
        assertThrows(IllegalArgumentException.class,
                () -> new Core.ResolvedPattern(one, null),
                "a carrier holding nothing is a refinement of its own, so no null stands for one");
        assertEquals(null, new Core.ResolvedPattern(one, new Refinement.OptionAbsent()).bindType(),
                "and the arm that selects it binds nothing readable, said by the refinement");
    }

    @Test
    void anArmSelectsSomething() {
        assertThrows(IllegalArgumentException.class,
                () -> new Core.ResolvedPattern(List.of(), new Refinement.OptionAbsent()));
    }
}
