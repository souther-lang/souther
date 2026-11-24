package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
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

import java.math.BigInteger;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A string two values bound — the case it is of takes lengths out, and the record above it places
 * an end — is not shown by what the case says of it alone. What a case takes out is the whole of
 * what is said of the string only where it is the one value that says anything; two together are
 * not proved, as two systems are not ({@code PlacedRules#proofAt}), so the strings are not shown
 * and no reader holds the lengths the case leaves where the record refuses them.
 *
 * <p>Asked of the same case with nothing said above it, to tell what leaves the strings unshown:
 * there they are shown, and are those of the lengths the case leaves.
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
                %s

            data Ok

            behavior read : (h: Holder) -> Ok
            """;

    private static String a(int length) {
        return "a".repeat(length);
    }

    /** The shared field under case A of a record whose own rule is {@code aboveIt}. */
    private static Position nameUnderA(String aboveIt) {
        Compilation compilation = ACompiledModel.compiles(
                Compilation.ofSources(List.of(MODEL.formatted(aboveIt)),
                        souther.compiler.meta.ModulePath.EMPTY));
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        RuleReadingContext reading =
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        InputDomain input = InputDomain.of(sigs.get("read"), reading,
                TypeCardinality.Counts.workedOutIn(reading),
                souther.compiler.carrier.Membership.none());
        for (Case each : input.at(TermPath.of("h").then("q")).obligationCases()) {
            if (each instanceof Case.SumCase one && one.leaf().name().equals("A")) {
                Position at = input.at(
                        TermPath.of("h").then("q").refine(Refinement.of(one)).then("name"));
                assertNotNull(at, "the shared field is a position under the case");
                return at;
            }
        }
        throw new AssertionError("no case A");
    }

    @Test
    void theStringsAreShownOfTheLengthsTheCaseLeavesWhereNothingIsSaidAboveIt() {
        StringsHeld.Held held = StringsHeld.held(nameUnderA(""));
        assertNotNull(held, "one value states the rule, and its runs are the whole of it");
        ValueSet strings = StringsHeld.asOneSet(held,
                PatternPlan.Budget.OF_THE_PIECES_OF_A_LANGUAGE.meter());
        assertNotNull(strings, "the strings of these lengths are a set this compiler makes");
        for (int length : List.of(6, 8, 20)) {
            assertTrue(held.lengths().holds(BigInteger.valueOf(length)), "length " + length);
            assertTrue(strings.has(new Value.Text(a(length))), "a string of " + length);
        }
        for (int length : List.of(7, 21)) {
            assertFalse(held.lengths().holds(BigInteger.valueOf(length)), "length " + length);
            assertFalse(strings.has(new Value.Text(a(length))), "a string of " + length);
        }
    }

    @Test
    void theStringsAreNotShownWhereTheRecordAboveStatesARuleOfItsOwn() {
        assertNull(StringsHeld.held(nameUnderA("invariant String.length(q.name) <= 10")),
                "two values state rules about it, and what the case takes out is not the whole");
    }
}
