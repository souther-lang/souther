package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ExpansionSite;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.ValueName;
import souther.compiler.types.WrittenOwner;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * A way is told apart by the rule it is, and not by the order the walk met its conditions in.
 *
 * <p>What a rule is is its columns and what each came out as, which {@link DecisionRule} answers as
 * a map. A path compared as the sequence it was collected in would be a second answer to that, and
 * the two would part over a body whose walk reaches one vector two ways — the reading of the ways
 * holds two arrivals apart when their paths differ, so it would carry one rule twice.
 *
 * <p>Written against the values rather than against a body, because what is under test is the
 * identity and not which bodies produce it. No source is known to reach one vector by two orders,
 * and that is why this is here: the law has to hold before anything does.
 */
class OneRuleIsOneWayHoweverTheWalkMetItsConditionsTest {

    private static final DecisionPath.Consulted OVER_FIVE = compared("a", 5, true);

    private static final DecisionPath.Consulted OVER_TEN = compared("b", 10, false);

    @Test
    void twoOrdersOfOneVectorAreOneWay() {
        DecisionPath one = way(OVER_FIVE, OVER_TEN);
        DecisionPath other = way(OVER_TEN, OVER_FIVE);
        assertEquals(one, other, "the same columns with the same answers are one way");
        assertEquals(one.hashCode(), other.hashCode(), "and hash alike");
        assertEquals(one.rule(), other.rule(), "which is the rule they are");
    }

    @Test
    void andTwoAnswersAboutOneColumnAreNot() {
        assertNotEquals(way(OVER_FIVE), way(compared("a", 5, false)),
                "one column coming out two ways is two ways");
    }

    /**
     * One column consulted at two calls of a helper is one column, and the way keeps both
     * consultations: where a run through each is seen and what each was read off.
     */
    @Test
    void oneColumnConsultedTwiceIsOneColumnWithBothConsultations() {
        ModelOccurrence first = comparisonIn(call(1));
        ModelOccurrence second = comparisonIn(call(2));
        DecisionPath.Consulted once = OVER_FIVE;
        DecisionPath.Consulted atTheFirst = seenAt(once, first);
        DecisionPath.Consulted atTheSecond = seenAt(once, second);

        DecisionPath both = way(atTheFirst, atTheSecond);
        assertEquals(way(atTheFirst), both, "the same column with the same answer is one rule");
        assertEquals(1, both.steps().size(), "and one condition of it");
        RuleStep step = both.steps().getFirst();
        assertEquals(List.of(atTheFirst.shown(), atTheSecond.shown()), step.seen(),
                "seen at both places the way consulted it, the first first");
        assertEquals(atTheFirst.shown(), step.shown(), "and witnessed where it was met first");
        assertEquals(List.of(first, second), step.said().copies(),
                "and read off both calls");
    }

    /**
     * What a condition consulted again asks is told the call it was asked at, entry for entry,
     * where the reading named each entry where it met it and the two are different values.
     */
    @Test
    void whatTheSecondConsultationAskedIsToldOfWhatTheFirstAsked() {
        ModelOccurrence first = comparisonIn(call(1));
        ModelOccurrence second = comparisonIn(call(2));
        DecisionPath.Consulted atTheFirst = seenAt(compared("a", 5, true, 0), first);
        DecisionPath.Consulted atTheSecond = seenAt(compared("a", 5, true, 1), second);
        assertNotEquals(atTheFirst.states(), atTheSecond.states(),
                "the two consultations' entries are two values");

        RuleStep step = way(atTheFirst, atTheSecond).steps().getFirst();
        assertEquals(List.of(first, second),
                step.said().entries().get(step.states().getFirst()),
                "what the way asks is read off both calls it was asked at");
    }

    /** {@code consulted}, which comes out holding, seen and read off at the comparison
     *  {@code at}. */
    private static DecisionPath.Consulted seenAt(DecisionPath.Consulted consulted,
                                                 ModelOccurrence at) {
        return new DecisionPath.Consulted(consulted.answer(), new ShownBy.AtAnOutcome(at, true),
                consulted.states(), ReachingCuts.Stating.of(consulted.states(), List.of(at)).by());
    }

    /** The comparison of the helper `positive` in its copy made at {@code made}. */
    private static ModelOccurrence comparisonIn(ExpansionLineage made) {
        return new ModelOccurrence(SourceConstructOrigin.written(
                new WrittenOwner.Body("m", "positive"), 1, SourceConstruct.BINARY), made);
    }

    /** The copy of `positive` the call at {@code ordinal} of the body makes. */
    private static ExpansionLineage call(int ordinal) {
        return ExpansionLineage.ORIGINAL.copiedInto(new ValueName.Helper("m", "positive"),
                new ExpansionSite.Written(SourceConstructOrigin.written(
                        new WrittenOwner.Body("m", "f"), ordinal, SourceConstruct.CALL)));
    }

    private static DecisionPath way(DecisionPath.Consulted... consulted) {
        DecisionPath out = DecisionPath.NOWHERE;
        for (DecisionPath.Consulted each : consulted) {
            out = out.and(each.answer(), each.shown(), each.states(), each.said());
        }
        return out;
    }

    /** One comparison of {@code head} against {@code against}, coming out {@code held}. */
    private static DecisionPath.Consulted compared(String head, int against, boolean held) {
        return compared(head, against, held, against);
    }

    /** The same, met by the reading as its condition {@code met}. */
    private static DecisionPath.Consulted compared(String head, int against, boolean held,
                                                   int met) {
        LinearForm<DecisionAtom> form =
                LinearForm.<DecisionAtom>atomMinusConstant(
                        new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of(head))),
                        ExactRatio.of(against));
        DecisionCondition.AComparison column = new DecisionCondition.AComparison(form, Rel.GT);
        return new DecisionPath.Consulted(new DecidedCondition.Compared(column, held),
                new ShownBy.NothingIsRecorded(column),
                List.of(new OnTheWay.Declined(
                        new ConditionOccurrence("b", ConditionOccurrence.Reading.DECIDING, met),
                        new ConditionReportAnchor.WhereTheReadingMetIt("b", new ConditionOccurrence(
                                "b", ConditionOccurrence.Reading.DECIDING, met)),
                        new WhyNotTaken.OutsideDomain(
                                WhyNotTaken.DomainLimit.A_QUANTITY_ON_NO_ORDER))),
                SaidOnTheWay.NONE);
    }
}
