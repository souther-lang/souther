package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.ValueName;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A clause written with a library predicate states of the numbers what the predicate means.
 *
 * <p>{@code String.isEmpty(s)} is a name for {@code String.length(s) == 0}, and a reading that took
 * a clause as the tree the backend emits from met the body that name expands to — a binding over a
 * comparison — rather than the operation, and made nothing of it. What the operation means is
 * declared beside the rest of what is true of the language's operations, and reaching it is a
 * question of which representation the clause arrives in.
 *
 * <p>Written for a family and not for one operation. What the settled form loses is every library
 * operation the analysis has a rule about, so a row here for {@code Bool.not} and one for a
 * container's own emptiness are the same claim asked of another name — and one of them passing
 * while another fails is what says the reading is recognising a spelling rather than an operation.
 */
class AnEmptinessCheckStatesWhatItMeansAboutTheLengthTest {

    /** What the rules leave the length of the one value the declaration is written on. */
    private static NumericDomain.Bounds lengthLeft(String carrier, String measure, String clause) {
        String source = """
                module example.rooms

                data Name = %s
                    invariant %s
                """.formatted(carrier, clause);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model under test compiles");
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        TypeSymbol.AtModule named = TypeSymbols.declared(new TypeKey(module, "Name"));
        assertNotNull(rules.symbols().declaredNode(named.key()), "no `Name` declared");
        String[] taken = measure.split("\\.");
        return FieldDomains.of(named, rules, ReadAs.THE_COMPILATION_DOES)
                .leftAt(RuleKey.THE_VALUE, new NumberAt.OfWhatNumber.OfWhatAnOperationAnswers(
                        ValueName.Stdlib.operation(taken[0], taken[1])));
    }

    private static void assertLength(NumericDomain.Bounds bounds, long least, long most) {
        assertNotNull(bounds, "the rules leave the length somewhere");
        assertNotNull(bounds.min(), "and say where it starts");
        assertNotNull(bounds.max(), "and where it stops");
        assertEquals(String.valueOf(least), bounds.min().at().toString(), "the least it may be");
        assertEquals(String.valueOf(most), bounds.max().at().toString(), "the most it may be");
    }

    /** The numeric form, which is what the other rows are read against. */
    @Test
    void aLengthWrittenAsANumberIsReadAsOne() {
        assertLength(lengthLeft("String", "String.length",
                "String.length(value) /= 0 && String.length(value) <= 9"), 1, 9);
    }

    @Test
    void anEmptinessCheckDeniedIsTheSameAsALengthThatIsNotNought() {
        assertLength(lengthLeft("String", "String.length",
                "String.isEmpty(value) == false && String.length(value) <= 9"), 1, 9);
    }

    @Test
    void andSoIsTheSameDenialWrittenAsACall() {
        assertLength(lengthLeft("String", "String.length",
                "Bool.not(String.isEmpty(value)) && String.length(value) <= 9"), 1, 9);
    }

    @Test
    void anEmptinessCheckAssertedHoldsTheLengthAtNought() {
        assertLength(lengthLeft("String", "String.length",
                "String.isEmpty(value) && String.length(value) <= 9"), 0, 0);
    }

    /**
     * And a declaration whose rules cannot both hold is refused.
     *
     * <p>The other half of reading the check as a number: a length that is not nought and is at
     * most nought is a model no value satisfies, and saying so is what a reading that takes the
     * emptiness in can do. Asserted through the diagnostic rather than through the range, because
     * a declaration with no value is what the author is told and the range is this compiler's
     * working.
     */
    @Test
    void rulesThatCannotBothHoldAreRefused() {
        Compilation compilation = Compilation.ofSource("""
                module example.rooms

                data Name = String
                    invariant String.isEmpty(value) == false && String.length(value) <= 0
                """, "Main");
        compilation.answerEverything();
        assertEquals(List.of("E1013"), compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList(),
                "no value satisfies both rules, and the declaration is refused for it");
    }
}
