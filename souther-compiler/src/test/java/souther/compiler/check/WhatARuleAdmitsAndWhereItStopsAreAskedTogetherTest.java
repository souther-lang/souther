package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.OrderedIntervals;
import souther.compiler.numeric.Text;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;
import souther.compiler.values.AdmissibleValues;
import souther.compiler.values.Allowance;
import souther.compiler.values.AsACompilationAllows;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule saying which values a position may take, beside one saying where its order stops.
 *
 * <p>Neither reading has a word for what the other holds. A pattern names no ends and an ordering
 * names no finite set, so a clause reaches whichever of them can say something about it and stays
 * there — and whether anything satisfies the rules was asked of each of them alone. Both answered
 * that something did, each about the half it could see.
 *
 * <p>What is asserted here is the proof and not the sentence. Where a position is left no value by
 * its set and its range together, that is what was shown: not an empty range, which is true of
 * neither half, and not a rule admitting nothing.
 */
class WhatARuleAdmitsAndWhereItStopsAreAskedTogetherTest {

    /** The rule this issue is written about: the strings from {@code "JP"} up, and the strings
     *  below {@code "JA"}. Nothing is in both. */
    @Test
    void aPatternAndACutBelowItShareNoString() {
        assertEquals(atTheValue(new Emptiness.NoAllowedValueInRange()), only("""
                module demo

                data Code = String
                    invariant no = String.startsWith("JP", value) && value < "JA"
                """));
    }

    /** And a cut the pattern reaches over is a rule somebody can satisfy. */
    @Test
    void aPatternAndACutItReachesOverAreARuleAValueSatisfies() {
        assertNull(only("""
                module demo

                data Code = String
                    invariant yes = String.startsWith("JP", value) && value < "JZ"
                """), "every string from `JP` up to `JQ` is below `JZ`");
    }

    /** A denial is a set and an equality is a range, which is the same pair said the short way. */
    @Test
    void aDeniedValueAndARangeHoldingOnlyThatValueShareNone() {
        assertEquals(atTheValue(new Emptiness.NoAllowedValueInRange()), only("""
                module demo

                data Code = String
                    invariant no = value /= "A" && value >= "A" && value <= "A"
                """));
    }

    /**
     * And over an enumeration, where the interval algebra carries nothing at all.
     *
     * <p>The same shape over an {@code Int} is refused by the numbers, which read both the denial
     * and the ends. That is the numbers answering and not the pair, so it says nothing about
     * whether the pair is asked — and every carrier the numbers do not hold was accepted.
     */
    @Test
    void aDeniedCaseAndAnOrderStoppingAtItShareNone() {
        assertEquals(atAField("q", new Emptiness.NoAllowedValueInRange()), only("""
                module demo

                data Ready
                data Done
                data Stage = Ready | Done

                data Held = { q: Stage }
                    invariant no = q /= Ready && q <= Ready
                """));
    }

    /**
     * Every alternative refused, each at a position the others stand at.
     *
     * <p>What the alternatives leave one position is their union, and the range at that position
     * holds a value of it: {@code x} may begin with {@code "A"}, which is below {@code "B"}, and
     * {@code y} may begin with {@code "D"}, which is at {@code "D"} or above. So a reading that
     * met the sets against the ranges position by position would find something at each of them and
     * nothing wrong anywhere — and no alternative survives, since the one that reaches {@code x} is
     * refused at {@code y} and the other way round.
     *
     * <p>No position is named, for the same reason: each of them holds values some alternative
     * stands at, so the lack is the whole product's. What is written is the general form, because
     * of where the alternatives are dropped — a branch nobody can be in is dropped while the
     * declaration is being settled, so by the time the whole is asked, the values admit nothing and
     * the proof is theirs.
     */
    @Test
    void alternativesRefusedAtDifferentPositionsLeaveNothingAndNameNoPosition() {
        assertEquals(new Emptiness.ConflictingRules(), only("""
                module demo

                data Held = { x: String, y: String }
                    invariant no = ((String.startsWith("A", x) && String.startsWith("B", y))
                        || (String.startsWith("C", x) && String.startsWith("D", y)))
                        && x < "B" && y >= "D"
                """));
    }

    /** And the same alternatives with one of them left standing are a rule somebody satisfies. */
    @Test
    void oneAlternativeStandingIsARuleAValueSatisfies() {
        assertNull(only("""
                module demo

                data Held = { x: String, y: String }
                    invariant yes = ((String.startsWith("A", x) && String.startsWith("B", y))
                        || (String.startsWith("C", x) && String.startsWith("D", y)))
                        && x < "B" && y >= "B"
                """), "the first alternative stands: `x` begins with `A` and `y` with `B`");
    }

    /**
     * Alternatives met with a range that reaches each position and no alternative of them.
     *
     * <p>The same shape as the model above, at the boundary where the two arrive apart: a reading
     * holding its alternatives, and ends put on the positions by rules read somewhere else. Nothing
     * settled the alternatives against those ends, so both are still standing when they meet, and
     * what each position holds across them reaches inside the range — {@code x} may be {@code "A"},
     * which is at {@code "A"} or below, and {@code y} may be {@code "D"}, which is at {@code "D"} or
     * above. Neither pair is: the one that reaches {@code x} is refused at {@code y}, and the other
     * way round.
     *
     * <p>Which is why the question is asked of every alternative and never of what they project onto
     * a position. Asked position by position, this state holds values.
     */
    @Test
    void alternativesAreAskedWholeAndNotThroughWhatTheyProjectOntoAPosition() {
        Allowance<FactSubject> sets = AsACompilationAllows.forAdmittedValues();
        AdmissibleValues<FactSubject> here = AdmissibleValues.at(X, ValueSet.just(Value.text("A")))
                .meet(AdmissibleValues.at(Y, ValueSet.just(Value.text("B"))), sets);
        AdmissibleValues<FactSubject> there = AdmissibleValues.at(X, ValueSet.just(Value.text("C")))
                .meet(AdmissibleValues.at(Y, ValueSet.just(Value.text("D"))), sets);
        ConstraintState<FactSubject> state = ConstraintState.<FactSubject>top()
                .takingValuesRead(here.joinApart(there, sets), sets)
                .taking(OrderedIntervals.at(X, new OrderedInterval(null,
                                Endpoint.inclusive(Text.of("A")))),
                        Map.of(X, Carrier.TEXT, Y, Carrier.TEXT))
                .taking(OrderedIntervals.at(Y, new OrderedInterval(
                                Endpoint.inclusive(Text.of("D")), null)),
                        Map.of(X, Carrier.TEXT, Y, Carrier.TEXT));

        assertEquals(ValueSet.oneOf(new LinkedHashSet<>(List.of(
                        Value.text("A"), Value.text("C")))), state.values().at(X),
                "each position holds a value the range reaches");
        assertTrue(state.confinement().ordered().at(X).admits(Text.of("A")));
        assertTrue(state.confinement().ordered().at(Y).admits(Text.of("D")));
        assertTrue(state.isBottom(), "and no alternative of them stands");
    }

    private static final Term.Interner NAMES = new Term.Interner();
    private static final FactSubject X = FactSubject.of(NAMES.written("x"));
    private static final FactSubject Y = FactSubject.of(NAMES.written("y"));

    private static Emptiness atTheValue(Emptiness under) {
        return new Emptiness.AtAField(new Emptiness.AtAField.Where.TheValueItself(), under);
    }

    private static Emptiness atAField(String spelled, Emptiness under) {
        return new Emptiness.AtAField(new Emptiness.AtAField.Where.In(spelled), under);
    }

    /** How the one declaration of {@code source} was shown to have no value, or null where it has
     *  one. */
    private static Emptiness only(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                        .flatMap(List::stream).map(each -> each.diagnostic().code().toString())
                        .filter(each -> !each.equals("E1013")).toList(),
                "the model this reads has to be one somebody could write");
        List<Hir.Def> defs = compilation.module("demo").defs().stream()
                .map(each -> each.declaration().node()).toList();
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
        String named = source.contains("data Code") ? "Code" : "Held";
        return TypeCardinality.solve(defs, RuleReadings.of(compilation, "demo"),
                        ReadAs.THE_COMPILATION_DOES)
                .of(TypeSymbols.declared(new TypeKey(symbols.module(), named))).why();
    }
}
