package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.TypeCardinality;
import souther.compiler.inputs.Case;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.regex.PatternPlan;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A string two values bound — the case it is of takes lengths out, and the record above it places
 * an end — holds the strings of the lengths both leave. What the case takes out is the whole of
 * what is said of it only where it is the only value that says anything; the two together are
 * not proved, as two systems are not, so the strings are either not shown or are those of the
 * lengths of both. Never the strings of the lengths one of them leaves and the other refuses.
 */
class ALengthTwoValuesBoundIsNotTakenFromOneOfThemTest {

    private static final String MODEL = """
            module layered

            data Paging = { name: String }
            data A = { ...Paging, x: Int }
                invariant String.length(name) <= 20 && String.length(name) /= 7
            data B = { ...Paging, y: Int }
            data Q = A | B

            data Holder = { q: Q }
                invariant String.length(q.name) <= 10

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    private static String a(int length) {
        return "a".repeat(length);
    }

    private static InputDomain reading() {
        Compilation compilation =
                Compilation.ofSources(List.of(MODEL), souther.compiler.meta.ModulePath.EMPTY);
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        return InputDomain.of(sigs.get("read"), reading,
                TypeCardinality.Counts.workedOutIn(reading),
                souther.compiler.carrier.Membership.none());
    }

    @Test
    void theStringsAreNotThoseOfTheLengthsOneOfTheTwoLeaves() {
        InputDomain input = reading();
        Position at = null;
        for (Case each : input.at(TermPath.of("h").then("q")).obligationCases()) {
            if (each instanceof Case.SumCase one && one.leaf().name().equals("A")) {
                at = input.at(TermPath.of("h").then("q").refine(Refinement.of(one)).then("name"));
            }
        }
        assertNotNull(at, "the shared field is a position under the case");

        StringsHeld.Held held = StringsHeld.held(at);
        if (held == null) {
            return;
        }
        // Made into one set, which is a machine of up to twenty code points here and is made.
        ValueSet strings = StringsHeld.asOneSet(held,
                PatternPlan.Budget.OF_THE_PIECES_OF_A_LANGUAGE.meter());
        assertNotNull(strings, "the strings of these lengths are a set this compiler makes");
        for (int length : List.of(7, 11)) {
            assertFalse(held.lengths().holds(java.math.BigInteger.valueOf(length)),
                    "the lengths include " + length);
            assertFalse(strings.has(new Value.Text(a(length))),
                    "the strings include one of " + length);
        }
        assertEquals(true, held.lengths().holds(java.math.BigInteger.valueOf(6)),
                "a string of six is one of the lengths both leave");
    }
}
