package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.Carrier;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.StatedContract;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.Membership;
import souther.compiler.observe.ObservedValue;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.observe.WorkFigure;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.regex.PatternPlan;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Text;
import souther.compiler.values.Allowance;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;
import souther.compiler.values.ValuesWithin;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a behavior's rules about the strings at a position divide it into, and what is said about the
 * ones that divide it into nothing.
 *
 * <p>The crossing from a rule to the values on either side of it. What comes out is two sets, both
 * built here and neither derived from the other by whoever holds them — so a reader downstream never
 * complements a language under an allowance of its own, and "the values it admits are known and the
 * rest are not" is a state with no spelling.
 *
 * <p><b>The position is the unit.</b> Two rules about one position are two distinctions of one
 * denominator, and a reader told about one of them is told about a partition the model does not
 * draw. So the rules of a position are built as one group, and a group that cannot be built leaves
 * the position divided by none of them.
 *
 * <p>And every rule that reaches here is answered for. The ones that divide come back as divisions
 * and the ones that do not come back as what became of them, which is what keeps a rule from
 * leaving without a sentence about it.
 */
class WhatABehaviorsRuleAboutItsStringsDividesAPositionIntoTest {

    /** Enough for the two sides of one of the rules written below, and not for two of them. The
     *  two assertions that say so are beside the one test this is for. */
    private static final PatternPlan.Budget ONE_RULE = new PatternPlan.Budget(1000, 60, 1_000_000_000L);

    @Test
    void aRuleAboutTheStringsDividesThePositionIntoWhatItAdmitsAndTheRest() {
        BehaviorSetStatements.Read read = readingsOf("""
                behavior f : (code: String) -> Answer
                let f (code) = if String.startsWith("JP", code) then Yes else No
                """);

        assertEquals(List.of(), read.blocked(), "the rule divides the position");
        SetStatement only = divisionIn(read);
        assertEquals(new NumericTerm.ValueOf(souther.compiler.inputs.TermPath.of("code")),
                only.term(), "the position the rule is written about");
        assertTrue(only.whenTrue().has(new Value.Text("JP-1")),
                "a string that satisfies the rule is on the side that does");
        assertFalse(only.whenFalse().has(new Value.Text("JP-1")),
                "and on no other");
        assertTrue(only.whenFalse().has(new Value.Text("US-1")),
                "and one that does not is on the side that does not");
        assertFalse(only.whenTrue().has(new Value.Text("US-1")),
                "and on no other");
    }

    /**
     * Two rules about one position are two divisions of it, built together.
     *
     * <p>Not two answers about one thing: the position is divided by both, and a reader given one of
     * them holds a partition the model does not draw.
     */
    @Test
    void twoRulesAboutOnePositionAreTwoDivisionsOfIt() {
        BehaviorSetStatements.Read read = readingsOf("""
                behavior f : (code: String) -> Answer
                let f (code) =
                    if String.startsWith("JP", code) then Yes
                    else if String.endsWith("X", code) then Yes else No
                """);

        assertEquals(List.of(), read.blocked(), "both rules divide the position");
        assertEquals(2, read.statements().size(), "and each of them is a division of it");
        assertEquals(1, read.statements().stream().map(RuleEvidence::at).distinct().count(),
                "of the one position both are written about");
    }

    /**
     * A rule an {@code ensures} states divides the position it is about.
     *
     * <p>Where the rule is written is not what makes it a division. A behavior's clause states what
     * the behavior is held to, and a clause about the strings at one of its inputs tells a set of
     * them from the rest exactly as a body's condition does — so the position is divided by it, and
     * read only in the body it would be a rule of the model this stage never heard.
     */
    @Test
    void aRuleAClauseStatesDividesThePositionItIsAbout() {
        BehaviorSetStatements.Read read = readingsOf("""
                behavior f : (code: String) -> Answer
                    ensures Yes -> String.startsWith("JP", code)
                let f (code) = Yes
                """);

        assertEquals(List.of(), read.blocked(), "the rule divides the position");
        SetStatement only = divisionIn(read);
        assertEquals(new NumericTerm.ValueOf(souther.compiler.inputs.TermPath.of("code")),
                only.term(), "the position the clause is written about");
        assertTrue(only.whenTrue().has(new Value.Text("JP-1")),
                "a string that satisfies the rule is on the side that does");
        assertTrue(only.whenFalse().has(new Value.Text("US-1")),
                "and one that does not is on the side that does not");
    }

    /**
     * A body and a clause writing about one position divide one position.
     *
     * <p>Two readers and one position. What the position is divided into is what the two rules come
     * to between them, so they meet before anything is built — read apart, the term would be
     * measured twice and each measure would hold a partition the model does not draw.
     */
    @Test
    void aBodyAndAClauseAboutOnePositionDivideOnePosition() {
        BehaviorSetStatements.Read read = readingsOf("""
                behavior f : (code: String) -> Answer
                    ensures Yes -> String.startsWith("JP", code)
                let f (code) = if String.endsWith("X", code) then Yes else No
                """);

        assertEquals(List.of(), read.blocked(), "both rules divide the position");
        assertEquals(2, read.statements().size(), "and each of them is a division of it");
        assertEquals(1, read.statements().stream().map(RuleEvidence::at).distinct().count(),
                "of the one position both are written about");
    }

    /**
     * And the two are one group, which is what an allowance affording one of them shows.
     *
     * <p>Enough to build the two sides of a single rule and no more. Read as two groups, the first
     * one asked would take the whole of it and divide the position while the second was refused —
     * so which rule a reader heard about would follow the order the two walks happened to run in.
     * As one group it is all of them or none, and the position is divided by neither.
     */
    @Test
    void aBodyAndAClauseAboutOnePositionAreOneGroup() {
        BehaviorSetStatements.Read read = readingsOf("""
                behavior f : (code: String) -> Answer
                    ensures Yes -> String.startsWith("JP", code)
                let f (code) = if String.endsWith("X", code) then Yes else No
                """,
                ONE_RULE);

        // What the allowance affords, said by the same allowance answering for each rule on its
        // own. Without these the two below would hold of an allowance that affords nothing, and
        // would say nothing about the grouping they are here for.
        assertEquals(1, readingsOf("""
                behavior f : (code: String) -> Answer
                    ensures Yes -> String.startsWith("JP", code)
                let f (code) = Yes
                """, ONE_RULE).statements().size(),
                "the allowance affords the clause on its own");
        assertEquals(1, readingsOf("""
                behavior f : (code: String) -> Answer
                let f (code) = if String.endsWith("X", code) then Yes else No
                """, ONE_RULE).statements().size(),
                "and the body's rule on its own");

        assertEquals(List.of(), read.statements(), "neither rule divides the position");
        // Every machine of the group is smaller than one may be, and what they come to together
        // is more than the group may make: the figure is the group's, at the numbers it was given.
        BlockReason.BehaviorDistinctionsTooCostly spent =
                new BlockReason.BehaviorDistinctionsTooCostly(
                        WorkFigure.BEHAVIOR_DISTINCTIONS_IN_ALL.at(
                                "60 states built and 1000000000 looked at"));
        assertEquals(List.of(spent, spent),
                read.blocked().stream().map(ClassingBlocker::why).toList(),
                "and both are answered for as the position's distinctions not being built, at"
                        + " the figure this run held them to");
    }


    /**
     * A rule every value satisfies divides nothing, and is said to.
     *
     * <p>Every string begins with the empty one, so one side of this holds every string and the
     * other holds none. What that comes to at the position is not this stage's answer: what a rule
     * leaves is a set of every string there is, and what the position holds is what its
     * declarations left it — so a side empty among the strings and a side empty at the position are
     * two facts, and only the second says the position is undivided.
     *
     * <p>So the rule is read and handed on, and nothing here is held open by it. Judged here, this
     * stage would be deciding a position's classes out of the strings, which is the authority it
     * does not have.
     */
    @Test
    void aRuleEveryStringSatisfiesIsStillHandedOn() {
        BehaviorSetStatements.Read read = readingsOf("""
                behavior f : (code: String) -> Answer
                let f (code) = if String.startsWith("", code) then Yes else No
                """);

        assertEquals(1, read.statements().size(), "the rule is read and handed on");
        assertEquals(List.of(), read.blocked(),
                "and nothing about the position's classes is held open by it");
    }

    /**
     * A rule about a value made from the position divides no position.
     *
     * <p>What it states is true of something the position was turned into, and there is no
     * denominator for it to divide: a class of the values here cannot be read off a class of what an
     * operation made from them.
     *
     * <p><b>And nothing is filed, because nothing places it.</b> A finding is shown at a position,
     * and the value this rule is about came from none that the reading can name — an operation
     * standing between the rule and the position is exactly what the reading has no path through. So
     * the rule is read, it divides nothing, and there is nowhere to say so.
     *
     * <p>Which is what the reading of a comparison does with the same shape
     * ({@link ComparisonAssessment}), and it is a limitation the two share rather than one of this
     * walk. Pinned here so that it is a fact somebody wrote down: an author writing this rule is
     * told nothing about it.
     */
    @Test
    void aRuleAboutAValueMadeFromThePositionDividesNoPosition() {
        BehaviorSetStatements.Read read = readingsOf("""
                behavior f : (code: String) -> Answer
                let f (code) = if String.startsWith("JP", String.trim(code)) then Yes else No
                """);

        assertEquals(List.of(), read.statements(), "no position is divided");
        assertEquals(List.of(), read.blocked(),
                "and nothing is filed, because the value it is about came from no position the"
                        + " reading can name");
    }

    /**
     * A position whose group cannot be built is divided by none of its rules.
     *
     * <p>The whole of why the position is the unit, shown with an allowance that affords neither.
     * Built one at a time, which of the two a reader heard about would follow the order the body
     * happened to be walked in — and the answer would be a partition of the position that the model
     * does not draw, rather than the position undivided.
     */
    @Test
    void aPositionWhoseGroupCannotBeBuiltIsDividedByNoneOfItsRules() {
        BehaviorSetStatements.Read read = readingsOf("""
                behavior f : (code: String) -> Answer
                let f (code) =
                    if String.startsWith("JP", code) then Yes
                    else if String.endsWith("X", code) then Yes else No
                """,
                // One state is fewer than the smallest of these rules needs, so the group is
                // refused where reading each of them was fine.
                new PatternPlan.Budget(1, 1, 1_000_000_000L));

        assertEquals(List.of(), read.statements(), "neither rule divides the position");
        // A machine of one state is smaller than any of these rules', so the first machine past it
        // is refused as a machine, at the one state this run allowed.
        BlockReason.BehaviorDistinctionsTooCostly refused =
                new BlockReason.BehaviorDistinctionsTooCostly(
                        WorkFigure.BEHAVIOR_DISTINCTIONS_ONE_MACHINE
                                .at("1 states or 1000000000 looked at"));
        assertEquals(List.of(refused, refused),
                read.blocked().stream().map(ClassingBlocker::why).toList(),
                "and both are answered for as the position's distinctions not being built");
    }

    /**
     * And where the allowance runs out after the rules were read, the position has no classes and
     * every rule that reached it is still answered for.
     *
     * <p>The two sides of each rule were built — this stage got that far — and what runs out is
     * meeting them with what the position itself holds, which is the further work of composing the
     * classes. So there is a state where a rule reached the measure, became a statement, and the
     * classes it would have made were never worked out.
     *
     * <p>What must not happen there is silence about the rule. The account this stage answers to is
     * over everything handed to it, so a rule left without a word is not a report that says less —
     * it is this compiler refusing its own measure. Which is what it did.
     */
    @Test
    void whereTheAllowanceRunsOutComposingTheRulesAreStillAnsweredFor() {
        // Read under an allowance that affords the rule's two sides, so this stage gets as far as
        // handing over a statement about the position.
        BehaviorSetStatements.Read read = readingsOf("""
                behavior f : (code: String) -> Answer
                let f (code) = if String.matches("[a-z]+", code) then Yes else No
                """, new PatternPlan.Budget(100, 100, 1_000_000_000L));
        assertEquals(1, read.statements().size(), "the rule was read and both its sides were built");
        assertEquals(List.of(), read.blocked(), "so nothing was held open before this point");

        // And composed under one that does not afford meeting them with what the position holds.
        Allowance<NumericTerm.FromOnePosition> spent =
                Allowance.of(new PatternPlan.Budget(1, 1, 1_000_000_000L));
        Classing.Result answered = Classing.of(read.statements().get(0).at(), read.statements(),
                List.of(), new Carrier.Text(),
                // A position whose own declarations leave it a language, which is what an
                // `invariant String.matches(...)` leaves. Meeting a rule with it is machine work,
                // and that is the work this allowance cannot afford.
                ((RuleEvidence.BySet) read.statements().get(0)).states().whenTrue().values(),
                spent, PatternPlan.Budget.OF_A_WITNESS::meter, place -> null);

        assertInstanceOf(Classing.Classed.NotComposed.class, answered.classed(),
                "the position has no classes");
        assertEquals(read.statements().size(), answered.forEach().size(),
                "and every rule that reached here is answered for, which is what the account that"
                        + " follows is owed: " + answered.forEach());
    }

    /**
     * A rule shown on its true side only as far as two code points, at a position whose values on
     * that side are all three long. No value is shown to hold the rule, and that is not that none
     * does: {@code abc} holds it and {@code ABC} does not, so the rule tells the two apart. It is
     * never one that tells nothing apart. Its classes are drawn over what it was shown on, which is
     * {@code ABC} alone, and {@code abc} is in none of them and left open.
     */
    @Test
    void aTrueSideShownOnlyShorterThanEveryValueOnItLeavesThemOpenAndNotUndivided() {
        Classing.Result answered = classedShownUpTo(matchingLowerCase(), 2L, ValueSet.oneOf(
                new LinkedHashSet<>(List.of(new Value.Text("abc"), new Value.Text("ABC")))),
                place -> null);

        assertEquals(List.of(Classing.Outcome.DIVIDED),
                answered.forEach().stream().map(Classing.Disposed::outcome).toList(),
                "a value open may be on the side no value is shown on");
        List<PartitionClass> classes = assertInstanceOf(Classing.Classed.Composed.class,
                answered.classed()).classes();
        assertEquals(1, classes.size(), "one class, of what was shown: " + classes);
        assertEquals(Membership.MATCH, Recognitions.membershipOf(
                classes.getFirst().recognises(), new ObservedValue.Text("ABC")));
        assertEquals(Membership.NO_MATCH, Recognitions.membershipOf(
                classes.getFirst().recognises(), new ObservedValue.Text("abc")));
        assertEquals(1, answered.leftOpen().size(), "and the one past the length is left open");
        assertTrue(answered.leftOpen().getFirst().open().stream()
                        .anyMatch(each -> each.has(new Value.Text("abc"))),
                "it is the value past the length: " + answered.leftOpen());
    }

    /**
     * The other way round: every value of the position is shown on the true side but one past the
     * length, and none on the false side. The rule may tell that one from the rest, so it is not
     * one that tells nothing apart, and its one class is the values it was shown to hold on.
     */
    @Test
    void aFalseSideHoldingNothingBesideValuesLeftOpenIsNotUndividedEither() {
        Classing.Result answered = classedShownUpTo(matchingLowerCase(), 3L, ValueSet.oneOf(
                new LinkedHashSet<>(List.of(new Value.Text("ab"), new Value.Text("abcd")))),
                place -> null);

        assertEquals(List.of(Classing.Outcome.DIVIDED),
                answered.forEach().stream().map(Classing.Disposed::outcome).toList());
        List<PartitionClass> classes = assertInstanceOf(Classing.Classed.Composed.class,
                answered.classed()).classes();
        assertEquals(1, classes.size(), "one class, of what was shown: " + classes);
        assertEquals(Membership.MATCH, Recognitions.membershipOf(
                classes.getFirst().recognises(), new ObservedValue.Text("ab")));
        assertEquals(1, answered.leftOpen().size());
    }

    /**
     * Every value of the position past the length the rule was shown to: none is shown on either
     * side, so there is no class to draw, and that is why the position has none. Nothing says the
     * rule tells nothing apart.
     */
    @Test
    void aPositionWhoseEveryValueIsLeftOpenHasNoClassForThatReason() {
        Classing.Result answered = classedShownUpTo(matchingLowerCase(), 2L, ValueSet.oneOf(
                new LinkedHashSet<>(List.of(new Value.Text("abc")))), place -> null);

        Classing.Classed.NotComposed none = assertInstanceOf(Classing.Classed.NotComposed.class,
                answered.classed());
        assertEquals(new BlockReason.RelationShownOverARegion(false, 2L, List.of()), none.why());
        assertEquals(List.of(Classing.Outcome.NOT_COMPOSED),
                answered.forEach().stream().map(Classing.Disposed::outcome).toList());
    }

    /**
     * Where the classes stop at a rule before it, what a rule leaves open is carried all the same.
     * The first rule's true side is {@code a} and a combining acute, which no value is shown to be
     * and none is shown not to be, so the classes are not composed; the second leaves the strings
     * past two code points open, and is still asked about them.
     */
    @Test
    void whatARuleLeavesOpenIsCarriedWhereTheClassesStopBeforeIt() {
        SetStatement read = matchingLowerCase();
        RuleEvidence unsettled = new RuleEvidence.BySet(new SetStatement(read.term(),
                ValuesWithin.all(matching("a\\x{301}")), read.whenFalse(), read.statement(),
                read.origin(), ValueSet.NONE));
        Classing.Result answered = Classing.of(read.term(),
                List.of(unsettled, shownUpTo(read, 2L)), List.of(),
                new Carrier.Text(), matching(".+"),
                Allowance.of(PatternPlan.Budget.OF_BEHAVIOR_DISTINCTIONS),
                PatternPlan.Budget.OF_A_WITNESS::meter, place -> null);

        assertInstanceOf(Classing.Classed.NotComposed.class, answered.classed());
        assertEquals(1, answered.leftOpen().size(), "the second rule's values past two: "
                + answered.leftOpen());
    }

    private static ValueSet matching(String regex) {
        PatternRead said = PatternParser.read(regex);
        return ValueSet.matching(PatternPlan.of(
                        assertInstanceOf(PatternRead.Read.class, said, regex).meaning())
                .compile(PatternPlan.Budget.OF_ADMITTED_VALUES.meter()));
    }

    /** The one division a rule that a code is lower case states. */
    private static SetStatement matchingLowerCase() {
        return divisionIn(readingsOf("""
                behavior f : (code: String) -> Answer
                let f (code) = if String.matches("[a-z]+", code) then Yes else No
                """));
    }

    /**
     * A class shown as far as three code points is stood for by a value it holds: the shortest
     * string within the length, and not the first the set names, which is past it.
     */
    @Test
    void aClassShownSoFarIsStoodForByAValueWithinIt() {
        SetStatement read = divisionIn(readingsOf("""
                behavior f : (code: String) -> Answer
                let f (code) = if String.matches("[a-z]+", code) then Yes else No
                """));
        List<Place> offered = new ArrayList<>();
        classedShownUpTo(read, 3L, ValueSet.oneOf(new LinkedHashSet<>(List.of(
                new Value.Text("abcdef"), new Value.Text("ab"), new Value.Text("AB")))),
                place -> {
                    offered.add(place);
                    return null;
                });

        assertTrue(offered.contains(Text.of("ab")), "the value within the length: " + offered);
        assertFalse(offered.contains(Text.of("abcdef")), "and not the one past it");
    }

    /**
     * Two rules at one position, each shown on its true side only so far: a value past either
     * length is in no class, and each rule says what it leaves open.
     */
    @Test
    void aValuePastWhereEitherOfTwoRulesIsShownIsInNoClass() {
        SetStatement read = divisionIn(readingsOf("""
                behavior f : (code: String) -> Answer
                let f (code) = if String.matches("[a-z]+", code) then Yes else No
                """));
        ValueSet admits = ValueSet.oneOf(new LinkedHashSet<>(List.of(new Value.Text("ab"),
                new Value.Text("abcd"), new Value.Text("abcdefg"), new Value.Text("AB"))));
        Classing.Result answered = Classing.of(read.term(),
                List.of(shownUpTo(read, 3L), shownUpTo(read, 5L)), List.of(),
                new Carrier.Text(), admits,
                Allowance.of(PatternPlan.Budget.OF_BEHAVIOR_DISTINCTIONS),
                PatternPlan.Budget.OF_A_WITNESS::meter, place -> null);

        List<PartitionClass> classes = assertInstanceOf(Classing.Classed.Composed.class,
                answered.classed()).classes();
        for (String value : List.of("abcd", "abcdefg")) {
            assertTrue(classes.stream().allMatch(each -> Recognitions.membershipOf(
                            each.recognises(), new ObservedValue.Text(value))
                            == Membership.NO_MATCH),
                    value + " is shown by neither rule and is in no class");
        }
        for (String value : List.of("ab", "AB")) {
            assertEquals(1, classes.stream().filter(each -> Recognitions.membershipOf(
                            each.recognises(), new ObservedValue.Text(value))
                            == Membership.MATCH).count(),
                    value + " is shown by both and is in one class");
        }
        assertEquals(2, answered.leftOpen().size(), "each rule leaves its own values open");
    }

    private static RuleEvidence shownUpTo(SetStatement read, long longest) {
        return new RuleEvidence.BySet(new SetStatement(read.term(),
                ValuesWithin.upTo(read.whenTrue().values(), longest), read.whenFalse(),
                read.statement(), read.origin(), ValueSet.NONE));
    }

    /** {@code read}, its true side shown only as far as {@code longest}, classed over a position
     *  holding {@code admits}. */
    private static Classing.Result classedShownUpTo(SetStatement read, long longest,
                                                    ValueSet admits,
                                                    Function<Place, FixtureTemplate> writing) {
        return Classing.of(read.term(), List.of(shownUpTo(read, longest)), List.of(),
                new Carrier.Text(), admits,
                Allowance.of(PatternPlan.Budget.OF_BEHAVIOR_DISTINCTIONS),
                PatternPlan.Budget.OF_A_WITNESS::meter, writing);
    }

    /** The one division the model under test states. */
    private static SetStatement divisionIn(BehaviorSetStatements.Read read) {
        assertEquals(1, read.statements().size(), "the model under test states one division");
        return ((RuleEvidence.BySet) read.statements().get(0)).states();
    }

    private static BehaviorSetStatements.Read readingsOf(String behavior) {
        return readingsOf(behavior, PatternPlan.Budget.OF_BEHAVIOR_DISTINCTIONS);
    }

    /** What {@code behavior}'s rules about its strings divide, built under {@code budget}. */
    private static BehaviorSetStatements.Read readingsOf(String behavior, PatternPlan.Budget budget) {
        String source = """
                module demo

                data Yes
                data No
                data Answer = Yes | No

                """ + behavior;
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(each -> each.diagnostic().code() + " " + each.diagnostic().primary())
                        .toList(),
                "the model under test compiles");
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        AnalysisBody body = checked.analysisBodies().get("f");
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get("f");
        assertNotNull(inputs, "the behavior under test is the one named");
        StatedContract stated =
                compilation.db().ask(new Bodies.StatedContracts(module)).value().get("f");
        PredicateReadings read = PredicateReadings.of("f", body, stated, inputs.reading(rules),
                inputs.parameterReads(), checked.elementBindings().get("f"),
                new RuleReachNumbering(module, "f"));
        Allowance<NumericTerm.FromOnePosition> allowance = Allowance.of(budget);
        return BehaviorSetStatements.of("f", read, inputs.reading(rules), allowance,
                List.of(), new RuleReachNumbering(rules.symbols().module(), "f"),
                WhatAnAnswerTakesUp.of(inputs.reading(rules)));
    }
}
