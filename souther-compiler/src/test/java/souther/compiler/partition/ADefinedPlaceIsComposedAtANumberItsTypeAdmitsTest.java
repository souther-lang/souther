package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.Symbols;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A place a rule defines as a number made of others is composed at a number its own type admits.
 *
 * <p>The number the factors come to is a number of the defined place only if the place's type
 * leaves it, and a type that admits a set of numbers inside its range leaves out the ones between.
 */
class ADefinedPlaceIsComposedAtANumberItsTypeAdmitsTest {

    private static final String SOURCE = """
            module demo

            data Restricted = Int
                invariant value == 1 || value == 3

            data N = { a: Int, b: Int, c: Restricted }
                invariant lower = a >= 1 && a <= 3
                invariant one = b == 1
                invariant product = c.value == a * b
            """;

    @Test
    void theFactorsAreChosenSoThatTheirProductIsOneTheTypeAdmits() {
        Partitions.FieldsChosen chosen = fieldsOfN();

        assertNotNull(chosen.fields(), "a of one or of three beside a b of one is such a record");
        String c = chosen.fields().get("c").text();
        String a = chosen.fields().get("a").text();
        assertTrue(c.equals("Restricted(1)") || c.equals("Restricted(3)"), c);
        assertTrue(a.equals("1") || a.equals("3"), "a is " + a + " beside c " + c);
    }

    private static Partitions.FieldsChosen fieldsOfN() {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main");
        compilation.answerEverything();
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
        TypeSymbol.AtModule record = TypeSymbols.declared(new TypeKey(symbols.module(), "N"));
        RuleReadingContext reading = RuleReadingContext.unshared(
                RuleReadings.of(compilation, "demo"), ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        return Partitions.fieldsOf(record, record, reading, Set.of(), Map.of());
    }
}
