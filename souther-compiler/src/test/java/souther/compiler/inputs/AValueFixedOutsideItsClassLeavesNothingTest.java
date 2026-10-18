package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.carrier.Membership;
import souther.compiler.meta.ModulePath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Dates;
import souther.compiler.numeric.Place;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value fixed where the class its declarations hold it to has no member leaves the input nothing,
 * and one fixed at a member does not.
 *
 * <p>The class is read beside the arithmetic and not in it. To the reading of numeric constraints
 * a remainder and a part of a date are numbers of their own, which nothing ties back to the value,
 * so fixing the value at fifteen hundred under a rule leaving it the multiples of a thousand is a
 * state that reading finds nothing wrong with. A search that holds a position to what the region
 * says of it asks the region, and a region that answered there was a value here would have the
 * search offer a row the declarations refuse.
 */
class AValueFixedOutsideItsClassLeavesNothingTest {

    private static final String HELD = """
            module g

            data Thousands = Int
                invariant Int.floorMod(value, 1000) == 0

            data Month = Date
                invariant Date.day(value) == 1

            data Ok

            behavior read : (t: Thousands, m: Month) -> Ok
            """;

    @Test
    void aRemainderFixedOutsideItsClassLeavesNothing() {
        assertTrue(fixedAt("t", Count.of(BigDecimal.valueOf(1500))).emptiness().isPresent());
        assertFalse(fixedAt("t", Count.of(BigDecimal.valueOf(2000))).emptiness().isPresent());
        assertFalse(fixedAt("t", Count.of(BigDecimal.valueOf(-3000))).emptiness().isPresent(),
                "a floor remainder leaves the class below nought as well");
    }

    @Test
    void aDateFixedOnADayItsClassHasNoneOfLeavesNothing() {
        assertTrue(fixedAt("m", Dates.dayOf("2024-05-15")).emptiness().isPresent());
        assertFalse(fixedAt("m", Dates.dayOf("2024-06-01")).emptiness().isPresent());
    }

    private static SearchRegion fixedAt(String spelled, Place at) {
        return READ.input().quantities(READ.rules()).region()
                .given(new NumericTerm.ValueOf(pathOf(spelled)), at);
    }

    private record Read(InputDomain input, RuleReadingSource rules) {}

    private static final Read READ = read();

    private static TermPath pathOf(String spelled) {
        return READ.input().positions().stream().map(Position::path)
                .filter(each -> each.toString().equals(spelled))
                .findFirst().orElseThrow(() -> new AssertionError(
                        "no position at " + spelled + " among " + READ.input().positions().stream()
                                .map(Position::path).toList()));
    }

    private static Read read() {
        Compilation compilation = Compilation.ofSources(List.of(HELD), ModulePath.EMPTY);
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES);
        return new Read(InputDomain.of(sigs.get("read"), reading,
                TypeCardinality.Counts.workedOutIn(reading), Membership.none()), rules);
    }
}
