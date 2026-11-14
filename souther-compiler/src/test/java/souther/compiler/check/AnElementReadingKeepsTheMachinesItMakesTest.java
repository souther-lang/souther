package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.TestDay;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.values.StringMachineAnswers;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a container states of every element is read of the element as a reading of its own, and a
 * reading keeps the machines it makes: what its counterfactual is handed is what the reading came
 * to, and one that came to nothing would build all of it again.
 *
 * <p>The element here is a string no declaration stands under, so there is no declaration to
 * borrow the machines under; they are the reading's own all the same.
 */
class AnElementReadingKeepsTheMachinesItMakesTest {

    /** Two statements of every string, one a pattern and one a length. */
    private static final String SOURCE = """
            module demo exposing ( Codes, keep )

            data Codes = List<String> invariant
                List.all(s -> String.matches("[A-Z]{2}-[0-9]{4}", s), value)
                && List.all(s -> String.length(s) <= 7, value)

            behavior keep : (c: Codes) -> Codes

            let keep (c) = c
            """;

    @Test
    void theCounterfactualMakesNoMachineTheElementsReadingHolds() {
        Compilation compilation = ACompiledModel.answered(SOURCE);
        RuleReadingContext reading = RuleReadingContext.of(
                RuleReadings.of(compilation, compilation.modules().get(0)),
                ReadAs.THE_COMPILATION_DOES, compilation.db().readings(), TestDay.TODAY);
        List<ElementGuarantee> stated = FieldDomains.of(
                TypeSymbols.declared(new TypeKey("demo", "Codes")), reading)
                .guaranteesAt(RuleKey.THE_VALUE);
        assertEquals(2, stated.size(), "the pattern and the length are statements of each string");

        long beforeReading = StringMachineAnswers.machinesMade();
        FieldDomains element = FieldDomains.ofElement(null, Type.STRING, stated, reading);
        long afterReading = StringMachineAnswers.machinesMade();
        assertTrue(afterReading > beforeReading,
                "reading the element builds the machine its pattern comes to");

        element.leavingOut(Set.of(stated.getLast().part()));

        assertEquals(afterReading, StringMachineAnswers.machinesMade(),
                "and the reading without the length answers its string questions out of it");
    }
}
