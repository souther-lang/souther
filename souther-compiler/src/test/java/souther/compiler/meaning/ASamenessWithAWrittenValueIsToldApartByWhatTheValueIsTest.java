package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.values.Operand;
import souther.compiler.values.Value;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * A statement of a subject being a value written is told from another by what the value is, and
 * not by how it is shown. Propositions are kept once, and put in order, by their spelling, so two
 * values that are two must not be spelled as one.
 */
class ASamenessWithAWrittenValueIsToldApartByWhatTheValueIsTest {

    private static final DecisionSubject SUBJECT = new DecisionSubject.AnInput(TermPath.of("x"));

    private static Proposition.SameValue against(Value value) {
        return new Proposition.SameValue(SUBJECT, new Operand.Written<>(value), true);
    }

    /** Two modules may each declare a case of one name: the cases are two values. */
    @Test
    void twoCasesOfOneNameInTwoModulesAreTwoValues() {
        TypeSymbol.AtModule here = TypeSymbols.declared(new TypeKey("here", "Active"));
        TypeSymbol.AtModule there = TypeSymbols.declared(new TypeKey("there", "Active"));

        assertEquals(Value.of(here).spelled(), Value.of(there).spelled(),
                "shown to a reader they are the one name");
        assertNotEquals(against(Value.of(here)).spelling(), against(Value.of(there)).spelling());
        assertNotEquals(against(Value.of(here)), against(Value.of(there)));
    }

    @Test
    void aValueWrittenTwoWaysIsOneValue() {
        assertEquals(against(Value.number(1)).spelling(),
                against(Value.number(new java.math.BigDecimal("1.0"))).spelling());
    }

    @Test
    void aTextAndANumberOfTheSameSpellingAreTwoValues() {
        assertNotEquals(against(Value.text("1")).spelling(), against(Value.number(1)).spelling());
    }
}
