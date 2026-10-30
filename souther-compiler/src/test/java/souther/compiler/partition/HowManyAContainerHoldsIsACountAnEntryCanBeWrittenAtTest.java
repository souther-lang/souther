package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * How many a container holds is a count a row takes only where that many entries can be written
 * together: an entry of a list or a set is its element, and one of a map is a key and a value, so
 * a map whose keys no value is holds nothing, whatever its values are. A set holds an element
 * once and a map a key, so a count of them is shown up to how many differ the element or key has:
 * the values it counts out, without end for a number or a string no rule is written on, and one
 * where a rule is. A list is shown up to whatever the rules leave.
 */
class HowManyAContainerHoldsIsACountAnEntryCanBeWrittenAtTest {

    /** A string of two characters that is three letters, which no value is. */
    private static final String NEVER = "data Never = String invariant String.length(value) == 2"
            + " && String.matches(\"[a-z]{3}\", value)";

    @Test
    void aMapIsHeldAtACountOnlyWhereBothItsKeyAndItsValueCanBeWritten() {
        assertEquals(List.of(true, true, true, true), heldAt("Map<String, Int>"));
        assertEquals(List.of(true, false, false, false), heldAt("Map<Never, Int>"));
        assertEquals(List.of(true, false, false, false), heldAt("Map<String, Never>"));
    }

    @Test
    void aListIsHeldAtEveryCountAndASetUpToHowManyItsElementsDiffer() {
        assertEquals(List.of(true, true, true, true), heldAt("List<Int>"));
        assertEquals(List.of(true, false, false, false), heldAt("List<Never>"));
        assertEquals(List.of(true, true, true, true), heldAt("Set<Int>"));
        assertEquals(List.of(true, true, true, false), heldAt("Set<Bool>"));
        assertEquals(List.of(true, false, false, false), heldAt("Set<Never>"));
    }

    /** A date is a type nothing counts out, and a rule written on a number leaves it one value
     *  the owner shows: neither is taken for a type with more than one. */
    @Test
    void aSetOfATypeNothingCountsOutOrARuleHoldsIsShownOneValue() {
        assertEquals(List.of(true, true, false, false), heldAt("Set<Date>"));
        assertEquals(List.of(true, true, false, false), heldAt("Set<Digit>"));
    }

    /** Whether a container of {@code type} is shown to be held at nought, one, two and three. */
    private static List<Boolean> heldAt(String type) {
        Compilation compilation = Compilation.ofSource("""
                module example.held

                %s
                data Digit = Int invariant value >= 1 && value <= 3
                data Holder = { c: %s }

                data Ok
                data No

                behavior check : (h: Holder) -> Ok | No

                let check (h) = Ok
                """.formatted(NEVER, type), "Main");
        assertEquals(List.of(), compilation.errors(), "the model compiles");
        String module = compilation.modules().get(0);
        InputDomain domain = compilation.db().ask(new Adequacy.Inputs(module)).value()
                .get("check");
        assertNotNull(domain, "the model compiles");
        InputReading reading = domain.reading(RuleReadings.of(compilation, module));
        NumericDomain.Bounds held = UndividedByARelation.howManyAreHeld(TermPath.of("h").then("c"),
                reading, reading.quantities().region());
        return List.of(0, 1, 2, 3).stream()
                .map(count -> held != null && held.admits(Count.of(count))).toList();
    }
}
