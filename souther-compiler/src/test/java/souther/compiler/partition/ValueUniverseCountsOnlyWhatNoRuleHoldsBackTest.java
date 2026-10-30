package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadings;
import souther.compiler.check.ValueUniverse;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.TermPath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * How many values a type has that differ is the values its rules leave, and not the values of
 * what it is made of.
 *
 * <p>A name wrapped round a boolean is two values to the reader of a rule that excludes some, and
 * one value to a reader asking how many the type has where the name says it is {@code true}. The
 * count is given for a type nothing is written on and for a name that carries no rule; anything a
 * rule is written on is not counted, which is minus one and not a smaller number.
 */
class ValueUniverseCountsOnlyWhatNoRuleHoldsBackTest {

    private static final String DECLARATIONS = """
            data A
            data B
            data C
            data Side = A | B | C
            data Flag = Bool
            data OnlyTrue = Bool invariant value == true
            data WrapsOnlyTrue = OnlyTrue
            data OnlyA = Side invariant value == A
            data Holder = {
                bool: Bool, flag: Flag, onlyTrue: OnlyTrue, wrapped: WrapsOnlyTrue,
                side: Side, onlyA: OnlyA, number: Int, date: Date
            }
            """;

    @Test
    void aTypeIsCountedOnlyWhereNoRuleIsWrittenOnIt() {
        assertEquals(2, countOf("bool"));
        assertEquals(2, countOf("flag"), "a name with no rule is the values it wraps");
        assertEquals(3, countOf("side"), "an enumeration has the cases it declares");
        assertEquals(-1, countOf("onlyTrue"), "one rule leaves one of the two, and none is counted");
        assertEquals(-1, countOf("wrapped"), "a rule under the name it wears is a rule on it");
        assertEquals(-1, countOf("onlyA"), "and over an enumeration the same");
        assertEquals(-1, countOf("number"), "a number has no end of values to count out");
        assertEquals(-1, countOf("date"));
    }

    private static long countOf(String field) {
        Compilation compilation = Compilation.ofSource("""
                module example.universe

                %s
                data Ok
                data No

                behavior check : (h: Holder) -> Ok | No

                let check (h) = Ok
                """.formatted(DECLARATIONS), "Main");
        assertEquals(List.of(), compilation.errors(), "the model compiles");
        String module = compilation.modules().get(0);
        InputDomain domain = compilation.db().ask(new Adequacy.Inputs(module)).value()
                .get("check");
        assertNotNull(domain, "the model compiles");
        InputReading reading = domain.reading(RuleReadings.of(compilation, module));
        return ValueUniverse.howManyDiffer(
                reading.domain().typeAt(TermPath.of("h").then(field), reading.rules()),
                reading.ruleReading());
    }
}
