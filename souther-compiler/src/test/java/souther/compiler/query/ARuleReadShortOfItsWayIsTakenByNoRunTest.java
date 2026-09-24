package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.coverage.AlignedObservation;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.Observation;
import souther.compiler.partition.AnswersDemanded;
import souther.compiler.partition.ConditionOccurrence;
import souther.compiler.partition.DecidedCondition;
import souther.compiler.partition.DecisionCondition;
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.DecisionRule;
import souther.compiler.partition.OnTheWay;
import souther.compiler.partition.RulesTaken;
import souther.compiler.partition.WayToTheBorder;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule read with fewer conditions than its way turns on is one no run is placed at, and the
 * reading it is in is short of it whether or not any row ran.
 *
 * <p>What a run is checked against is the conditions the path carries. Where the path is not whole,
 * a run seen doing all of them has not been shown to have taken the rule, and a path with none left
 * is matched by every run — which puts every run at that rule as well as at the one it took.
 *
 * <p>Held beside the rule with no conditions that is whole, because the two are not the same
 * thing: a body that draws no distinction has one rule and every run takes it. Asking whether the
 * path is empty would set that one aside too.
 *
 * <p>And that a rule was read short is a fact about how the rules were derived, which is settled
 * before any row runs. Read only where a run meets the rules, it would be lost wherever no row ran,
 * and a behavior nobody wrote a row for would be measured as complete over a rule it did not read.
 */
class ARuleReadShortOfItsWayIsTakenByNoRunTest {

    /** A body with no fork, which is all a plan and a tree are needed for here. */
    private static final String MODEL = """
            module demo
            data Yes
            behavior decides : (a: Int) -> Yes
            let decides (a) = Yes
            """;

    private static final DecisionRule NO_DISTINCTION = new DecisionRule(Map.of());

    /** A rule that turns on one condition this reading has no words for, so it is not
     *  {@link #NO_DISTINCTION} and a finding about one is not a finding about the other. */
    private static final DecisionRule ONE_DISTINCTION = new DecisionRule(Map.of(
            new DecisionCondition.AConditionNotRead(new ConditionOccurrence("decides", 0),
                    new OnTheWay.Why.NoWordsForTheShape()),
            new DecidedCondition.Unread(new DecisionCondition.AConditionNotRead(
                    new ConditionOccurrence("decides", 0), new OnTheWay.Why.NoWordsForTheShape()),
                    true)));

    @Test
    void aPathThatIsNotWholeIsSetAside() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        assertEquals(new RulesTaken.WhichRule.CouldNotTell(
                        RulesTaken.WhichRule.Why.NO_RULE_IS_RECOGNISABLE),
                rulesOf(compilation, reading(ruled(NO_DISTINCTION, false)))
                        .takenBy(nothingSeen(compilation)));
    }

    @Test
    void aWholePathWithNoConditionIsTakenByEveryRun() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        assertEquals(new RulesTaken.WhichRule.TookThis(NO_DISTINCTION),
                rulesOf(compilation, reading(ruled(NO_DISTINCTION, true)))
                        .takenBy(nothingSeen(compilation)));
    }

    /**
     * With no row at all, a reading holding a rule read short is not a complete measurement.
     *
     * <p>No run is placed and none is left unplaced, so nothing about the runs weakens it. What
     * does is the rule, and it is there whatever the rows are.
     */
    @Test
    void aReadingWithNoRowsIsStillShortOfARuleItReadShort() {
        DecisionEvidence evidence = evidenceWithNoRows(reading(ruled(NO_DISTINCTION, false)));
        assertInstanceOf(Measurement.Partial.class, evidence.took(),
                () -> "a reading with a rule read short is not complete: " + evidence.took());
        assertEquals(WeakeningSet.of(new Weakening.DecisionRuleReadShort("decides")),
                evidence.weakening(), "and what it went without is that rule");
    }

    /** And the control: the same reading with the rule read in full is complete. */
    @Test
    void aReadingWithNoRowsAndEveryRuleWholeIsComplete() {
        DecisionEvidence evidence = evidenceWithNoRows(reading(ruled(NO_DISTINCTION, true)));
        assertInstanceOf(Measurement.Complete.class, evidence.took(),
                () -> "nothing was read short and no row was left unplaced: " + evidence.took());
    }

    /**
     * A rule read short bears on that rule, and a rule read in full beside it is not left undecided
     * by it.
     *
     * <p>The ways through a body are exclusive, so a rule read in full that no row took is a rule no
     * row took however its neighbour was read.
     */
    @Test
    void aRuleReadShortBearsOnItselfAndNotOnARuleBesideIt() {
        DecisionReading.Ruled whole = ruled(NO_DISTINCTION, true);
        DecisionReading.Ruled readShort = ruled(ONE_DISTINCTION, false);
        DecisionEvidence evidence = evidenceWithNoRows(reading(whole, readShort));

        assertEquals(WeakeningSet.none(), evidence.at(whole).weakening(),
                "the rule read in full rests on nothing its neighbour went without");
        assertEquals(WeakeningSet.of(new Weakening.DecisionRuleReadShort("decides")),
                evidence.at(readShort).weakening(), "and the rule read short rests on that");

        assertEquals(Adequacy.Finding.Disposition.UNDECIDED,
                findingAbout(evidence, readShort).disposition(),
                "so a finding about the rule read short is undecided and refuses no build");
        assertTrue(findingAbout(evidence, whole).isAdequacyGap(),
                "and one about the rule read in full is the gap the rows established");
    }

    private static Adequacy.Finding findingAbout(DecisionEvidence evidence,
                                                 DecisionReading.Ruled ruled) {
        return Adequacy.Finding.by(new FindingSubject.OfABehavior("decides"), evidence.at(ruled),
                new About.ARuleNoRowTakes("decides", ruled));
    }

    private static DecisionReading.Ruled ruled(DecisionRule rule, boolean whole) {
        return new DecisionReading.Ruled(rule, List.of(), WayToTheBorder.UNTOUCHED,
                AnswersDemanded.NOTHING, whole);
    }

    private static DecisionReading reading(DecisionReading.Ruled... found) {
        return new DecisionReading("decides", List.of(found),
                new DecisionReading.Enumeration.Complete());
    }

    /** What the rows of {@code read} took where nobody wrote a row, as the account makes it. */
    private static DecisionEvidence evidenceWithNoRows(DecisionReading read) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        return new DecisionEvidence(read, DecisionEvidence.of("decides",
                rulesOf(compilation, read), List.of(), WeakeningSet.none()));
    }

    private static RulesTaken rulesOf(Compilation compilation, DecisionReading read) {
        Bodies.Elaborated checked = checkedOf(compilation);
        return RulesTaken.of(read, checked.behaviorBodies().get("decides"), checked.plan());
    }

    /** A run that was seen doing nothing, under the numbering of this compilation. */
    private static AlignedObservation nothingSeen(Compilation compilation) {
        CoverageSites.Plan plan = checkedOf(compilation).plan();
        return plan.numbering().align(
                new Observation(plan.numbering().identity(), Set.of(), Set.of()));
    }

    private static Bodies.Elaborated checkedOf(Compilation compilation) {
        return compilation.db().ask(new Bodies.Checked(compilation.modules().get(0))).value();
    }
}
