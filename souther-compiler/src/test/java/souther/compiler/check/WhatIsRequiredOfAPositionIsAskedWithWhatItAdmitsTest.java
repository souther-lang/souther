package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.lang.reflect.RecordComponent;
import java.math.BigDecimal;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule leaving a position a set of values, beside rules that require it to lie somewhere.
 *
 * <p>Neither reading holds the other's half. A choice is read where the values and the ends are,
 * and the numbers relate a position to its neighbours and read no branch — so the bound a choice
 * leaves is one the numbers never see, and the bound a relation derives is one no alternative is
 * ever met with. Each is sound alone, and whether anything satisfies them together was asked of
 * each of them by itself.
 *
 * <p>What is asserted here is the proof and not the sentence, and which reading showed it: a
 * declaration whose own values and ends share nothing is shown by those two, and one whose values
 * are fine until what the rules require of the position is asked with them is shown by neither.
 */
class WhatIsRequiredOfAPositionIsAskedWithWhatItAdmitsTest {

    /** The rule this issue is written about: a choice leaving {@code x} at one or two, and a
     *  relation leaving it at three or above. */
    @Test
    void aChoiceAndARelationThatShareNoValueAdmitNothing() {
        assertEquals(atAField("x", new Emptiness.NoAllowedValueWithinRequiredBounds()), only("""
                module demo

                data Held = { x: Int, y: Int }
                    invariant no = (x == 1 || x == 2)
                                && x == y + 1
                                && y >= 2
                """));
    }

    /**
     * And the same rules written as a conjunction, which is the whole point of the one above.
     *
     * <p>Refused by the numbers alone, since a bound written that way is one they read — so what
     * this holds is that the two spellings are answered alike. Written as a choice and read without
     * the reduction, the second was accepted and the first refused, and which of them an author
     * wrote is not a difference the model states.
     */
    @Test
    void andTheSameRulesWrittenAsAConjunctionAreRefusedToo() {
        assertEquals(new Emptiness.ConflictingRules(), only("""
                module demo

                data Held = { x: Int, y: Int }
                    invariant no = x >= 1 && x <= 2 && x == y + 1 && y >= 2
                """));
    }

    /** The same over an order the model does not add on, where the relation is an operation's. */
    @Test
    void datesAreTheSameShapeOverAnOrderTheModelDoesNotAddOn() {
        assertEquals(atAField("a", new Emptiness.NoAllowedValueWithinRequiredBounds()), only("""
                module demo

                data Span = { a: Date, b: Date }
                    invariant no = (a == Date("2020-01-01") || a == Date("2020-01-02"))
                                && Date.daysBetween(a, b) >= 1
                                && b <= Date("2010-01-01")
                """));
    }

    /**
     * A bound written on the position itself is still the order's own proof.
     *
     * <p>The reduction is asked only where every reading of the state left something, so a
     * declaration one of them refuses is refused by it and told in its words. Asked the other way
     * round, this model would be reported against bounds derived from the rule the author wrote at
     * {@code x}, which is true and is further from what they have to change.
     */
    @Test
    void aBoundWrittenOnThePositionIsStillTheOrdersOwnProof() {
        assertEquals(atAField("x", new Emptiness.EmptyOrderedInterval()), only("""
                module demo

                data Held = { x: Int, y: Int }
                    invariant no = (x == 1 || x == 2) && x >= 3 && y == 0
                """));
    }

    /**
     * Every alternative outside what the rules require, where what they leave between them is not.
     *
     * <p>What makes this a reduction over the alternatives rather than over what they come to. The
     * two alternatives leave {@code x} at one and at seven, and the bounds the relation derives are
     * three to five: neither alternative is inside them, and the smallest range holding both of
     * them is. So an implementation that met the requirement against what the position admits
     * across the alternatives finds a value at each end and refuses nothing.
     */
    @Test
    void everyAlternativeOutsideWhatIsRequiredIsRefusedThoughWhatTheyShareIsNot() {
        assertEquals(atAField("x", new Emptiness.NoAllowedValueWithinRequiredBounds()), only("""
                module demo

                data Held = { x: Int, y: Int }
                    invariant no = (x == 1 || x == 7) && x == y + 1 && y >= 2 && y <= 4
                """));
    }

    /**
     * Positions the rules hold as one value, refused as the one value they are.
     *
     * <p>The block and not its members. Each of {@code p} and {@code r} is left something on its
     * own — {@code p} may be one and {@code r} may be nine — and what has nothing is the one value
     * the alternative says they are, since what is required of them cannot both hold of it.
     *
     * <p>An equality inside an alternative, because that is the only place a block's members can be
     * required to be in different ranges: written outside one, the numbers read the same equality
     * and refuse the rules on their own.
     */
    @Test
    void positionsHeldAsOneValueAreRefusedAsThatValue() {
        assertEquals(new Emptiness.AtEqualPositions(
                        List.of(new Emptiness.AtAField.Where.In("p"),
                                new Emptiness.AtAField.Where.In("r")),
                        new Emptiness.NoAllowedValueWithinRequiredBounds()), only("""
                module demo

                data Held = { p: Int, r: Int, s: Int, t: Int }
                    invariant no = ((p == r && p == 1) || (p == r && p == 9))
                                && s == p + 1 && s <= 4
                                && t == r - 1 && t >= 7
                """));
    }

    /** And one alternative inside them is a rule somebody satisfies. */
    @Test
    void anAlternativeInsideThemIsARuleAValueSatisfies() {
        assertNull(only("""
                module demo

                data Held = { x: Int, y: Int }
                    invariant yes = (x == 1 || x == 7) && x == y + 1 && y >= 6 && y <= 8
                """), "seven is one past a six the rules admit");
    }

    /** A position on an order that counts nothing is left where it was: no number stands under a
     *  string, so nothing about one is required of it here. */
    @Test
    void aPositionOnAnOrderThatCountsNothingIsLeftWhereItWas() {
        assertNull(only("""
                module demo

                data Held = { x: String, y: String }
                    invariant yes = (x == "a" || x == "b") && y >= "m"
                """));
    }

    /**
     * A correlation an alternative states, against a relation between the same two positions.
     *
     * <p>Not read, and the boundary is the mechanism's rather than a gap in it. What is met with an
     * alternative is what each position must lie between, one position at a time, and a relation
     * between two of them leaves each of them everything: {@code x == y + 1} bounds neither. So the
     * pairs an alternative states are not asked about, and the declaration below is admitted though
     * neither pair satisfies the relation.
     *
     * <p>Closing it is a reduction over the product of the positions rather than over each of them,
     * which is another question and is not this one. Held here so that the day it is answered, what
     * changed is the precision of a reading and not a defect somebody found.
     */
    @Test
    void aCorrelationAnAlternativeStatesIsNotAskedOfTheNumbers() {
        assertNull(only("""
                module demo

                data Held = { x: Int, y: Int }
                    invariant no = ((x == 1 && y == 1) || (x == 2 && y == 2)) && x == y + 1
                """), "neither pair satisfies the relation, and no position is refused on its own");
    }

    /**
     * A value settled after the declaration was read is asked against what that settling requires.
     *
     * <p>The other lifetime of the same question. What the rules require of a position is a fact
     * about a state, so a state with one more fact in it has a requirement of its own — and the
     * envelope a reading was answered under is not carried to it. Carried, the alternatives here
     * would be met with what was required before anybody settled anything, and a row would be
     * offered at a value the declaration cannot hold.
     */
    @Test
    void aValueSettledAfterwardsIsAskedAgainstWhatItRequires() {
        assertTrue(settling(3), "x is one of one and seven, and the rules leave it at three");
        assertFalse(settling(7), "seven is one of them");
    }

    /** What {@link NumericDomain} says about a position, which is three answers and not two. */
    @Test
    void aDomainSaysNothingAboutAnAtomAndSaysWhereOneIsWithNoEnds() {
        NumericDomain<String> nothing = NumericDomain.top();
        assertInstanceOf(NumericDomain.Projection.NotSpokenOf.class, nothing.projectionOf("x"),
                "no rule names it, so nothing about it follows from these rules");
        NumericDomain<String> related = nothing.assume(
                LinearForm.<String>atom("x").minus(LinearForm.atom("y")), Rel.EQ,
                Map.of("x", souther.compiler.numeric.Granularity.DISCRETE,
                        "y", souther.compiler.numeric.Granularity.DISCRETE));
        assertEquals(new NumericDomain.Projection.Within(new NumericDomain.Bounds(null, null)),
                related.projectionOf("x"),
                "a rule names it and places no end, which is not the same as no rule naming it");
        NumericDomain<String> nowhere = related.assume(
                LinearForm.<String>constant(BigDecimal.ONE), Rel.LT,
                Map.of("x", souther.compiler.numeric.Granularity.DISCRETE));
        assertInstanceOf(NumericDomain.Projection.NothingIsLeft.class, nowhere.projectionOf("x"),
                "an atom of rules nothing satisfies is at no value, not at every value");
    }

    /** And which orders a count crosses into is the carrier's answer, asked of what it counts. */
    @Test
    void aCountCrossesIntoAnOrderThatCountsAndIntoNoOther() {
        NumericDomain.Bounds bounds = new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(1)), Endpoint.inclusive(Count.of(3)));
        assertEquals(new PositionRestriction.Within(new OrderedInterval(
                        Endpoint.inclusive(Count.of(1)), Endpoint.inclusive(Count.of(3)))),
                new Carrier.Whole().within(bounds));
        assertEquals(new PositionRestriction.Within(new OrderedInterval(
                        Endpoint.inclusive(Count.of(1)), Endpoint.inclusive(Count.of(3)))),
                new Carrier.Ordinal(TypeSymbols.declared(new TypeKey("demo", "Stage")), List.of())
                        .within(bounds),
                "an enumeration counts its places, so a bound in that count is one of its values");
        assertEquals(new PositionRestriction.NotSpokenOf(), new Carrier.Text().within(bounds),
                "a string stands in an order and no number stands under it");
    }

    /**
     * Every component of a state answers whether it places a position.
     *
     * <p>The roster and not the walk, which is {@code ConstraintState.positionEnvelope}'s and stops
     * on a component nobody answered for. Here so that adding one is a test somebody reads rather
     * than an exception somebody meets: what a component contributes is a decision, and the three
     * it can be are contributing a bound, having no bound to contribute, and being what the bounds
     * are asked of.
     */
    @Test
    void aComponentAddedToAStateSaysWhichOfTheThreeItIs() {
        assertEquals(List.of("numbers", "facts", "confinement", "shown"),
                Arrays.stream(ConstraintState.class.getRecordComponents())
                        .map(RecordComponent::getName).toList(),
                "a component added here answers, in `positionEnvelope`, whether it requires a"
                        + " position to be somewhere, has nothing to say about where one is, or is"
                        + " what such a requirement is asked of");
    }

    private static final String CHOICE = """
            module demo

            data Held = { x: Int, y: Int }
                invariant yes = (x == 1 || x == 7) && x == y
            """;

    /** Whether nothing satisfies {@link #CHOICE} once {@code y} is settled at {@code at}. */
    private static boolean settling(int at) {
        Compilation compilation = Compilation.ofSource(CHOICE, "Main");
        compilation.answerEverything();
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
        FieldDomains domains = FieldDomains.of(named(symbols, "Held"),
                RuleReadings.of(compilation, "demo"), ReadAs.THE_COMPILATION_DOES);
        Map<NumberAt<RuleKey>, Count> fixed = new LinkedHashMap<>();
        fixed.put(NumberAt.valueOf(RuleKey.of("y")), new Count(BigDecimal.valueOf(at)));
        return domains.given(fixed)
                .constraintsOver(claim -> "at:" + claim, other -> "other:" + other)
                .constraints().isBottom();
    }

    /** What the one declaration of {@code source} was shown to have no value by, or null. */
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
        return TypeCardinality.solve(defs, RuleReadings.of(compilation, "demo"),
                        ReadAs.THE_COMPILATION_DOES)
                .of(named(symbols, source.contains("data Span") ? "Span" : "Held")).why();
    }

    private static TypeSymbol.AtModule named(Symbols symbols, String data) {
        return TypeSymbols.declared(new TypeKey(symbols.module(), data));
    }

    private static Emptiness atAField(String spelled, Emptiness under) {
        return new Emptiness.AtAField(new Emptiness.AtAField.Where.In(spelled), under);
    }
}
