package souther.compiler.partition;

import souther.compiler.DefaultStdlib;
import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.coverage.ArmProbe;
import souther.compiler.coverage.Numberings;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeCardinality;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.query.ReadAs;
import souther.compiler.reading.PathAccess;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What the runs of one plan may disagree about is what each of them composed, and nothing else.
 *
 * <p>One run stands the dependencies in one way and the next another, and what that reaches is a
 * row: whether a value could be composed, and which arms the run of it was seen going through.
 * Everything beside that is read off the model and the body before any run is made, so two runs
 * differing there would mean the reading had come to depend on what a run was given — and an answer
 * taken from one of them would be an answer about that run reported as an answer about the model.
 *
 * <p>Refused rather than chosen between. A disagreement here is this compiler being inconsistent
 * with itself, which a reader cannot act on and should not be shown one half of.
 */
class TwoRunsOfOnePlanThatDisagreeAboutWhatTheyReadAreRefusedTest {

    private static final RuleReadingSource SYMBOLS =
            RuleReadings.ofNoClauseFiled(Symbols.none(DefaultStdlib.get()));

    private static final Map<Integer, ArmProbe> PLACES = Numberings.arms(3);

    private static final ClassOfAPosition A_CLASS =
            new ClassOfAPosition(new AxisId("fee", "days"), "days/low");

    private static final CameToNothing NO_CANDIDATE =
            CameToNothing.metNothing(new Generator.UnresolvedCombination(List.of("days=low"),
                    Generator.UnresolvedCombination.Reason.NO_CANDIDATE_WAS_OFFERED));

    private static final CameToNothing PROVED =
            CameToNothing.metNothing(new Generator.UnresolvedCombination(List.of("days=low"),
                    Generator.UnresolvedCombination.Reason.NO_VALUE_CAN_STAND_THERE));

    private static final Set<CompositionBudget> LEFT =
            Set.of(CompositionBudget.SEARCHES_A_ROW_IS_COMPOSED_THROUGH);

    private static final CameToNothing NOTHING_COMPOSES_ONE =
            CameToNothing.metNothing(new Generator.UnresolvedCombination(List.of("days=low"),
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE));

    private static final PathAccess NOTHING_ARRIVES = new PathAccess.Unreachable(
            PathAccess.Unreachable.Why.THE_CONDITION_NEVER_COMES_OUT_THAT_WAY);

    private static final PathAccess NO_WAY_CAN_BE_NAMED = new PathAccess.Unsupported(
            PathAccess.Unsupported.Why.NO_WAY_IN_CAN_BE_NAMED);

    /**
     * What a class nothing came of says is what the strategies made of the class, which no
     * stand-in reaches.
     */
    @Test
    void twoReasonsForAClassNoRunComposedARowForAreRefused() {
        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> ClassDisposition.acrossRuns(List.of(
                        new ClassDisposition.Unresolved(NO_CANDIDATE),
                        new ClassDisposition.Unresolved(NOTHING_COMPOSES_ONE))));

        assertEquals(true, refused.getMessage().contains("NO_CANDIDATE_WAS_OFFERED"),
                refused.getMessage());
    }

    /** And what the reading made of an arm nothing was tried at, for the same reason. */
    @Test
    void twoReadingsOfAnArmNoRunHadAnywhereToLookForAreRefused() {
        assertThrows(IllegalStateException.class,
                () -> ArmDisposition.acrossRuns(List.of(
                        new ArmDisposition.NoWayIn(NOTHING_ARRIVES),
                        new ArmDisposition.NoWayIn(NO_WAY_CAN_BE_NAMED))));
    }

    /**
     * An arm nothing can be steered to is an arm nothing can have failed at.
     *
     * <p>A reason for finding no row is written where the reading gave a way in to try, and the
     * reading is the same for every run. So a run that has one and a run that had nowhere to look
     * are reading one body two ways, which is not a pair of findings to carry together.
     */
    @Test
    void anArmOneRunHadNowhereToLookForAndAnotherHadAReasonAboutAreRefused() {
        assertThrows(IllegalStateException.class,
                () -> ArmDisposition.acrossRuns(List.of(
                        new ArmDisposition.NoWayIn(NOTHING_ARRIVES),
                        new ArmDisposition.Unresolved(List.of(NO_CANDIDATE)))));
    }

    /**
     * And a third run composing a row does not settle it.
     *
     * <p>What a reading gives a run to try is read before any run is made, so two runs reading one
     * arm two ways are in contradiction whatever a third found. Asked only where no row was
     * composed, the check would pass on exactly the arms a row makes a reader look at.
     */
    @Test
    void aRowComposedByAThirdRunDoesNotSettleThatDisagreement() {
        assertThrows(IllegalStateException.class,
                () -> ArmDisposition.acrossRuns(List.of(
                        new ArmDisposition.NoWayIn(NOTHING_ARRIVES),
                        new ArmDisposition.Unresolved(List.of(NO_CANDIDATE)),
                        new ArmDisposition.Built(new RowId(0), PLACES.get(1)))));
    }

    /**
     * And the runs have to have been asked the same question.
     *
     * <p>Answers to two plans joined would report one behavior's obligations as answered by what
     * was never asked about them. A caller holding two is holding two questions, which is why this
     * is refused as something asked for rather than as something this compiler got wrong.
     */
    @Test
    void runsOfTwoPlansAreNotJoined() {
        FillResult here = nothingCameOfIt(planOver(List.of(A_CLASS), 1));
        FillResult elsewhere = nothingCameOfIt(planOver(List.of(A_CLASS), 2));

        assertThrows(IllegalArgumentException.class,
                () -> FillResult.acrossRuns(List.of(here, elsewhere)));
    }

    /**
     * And there have to be runs to join.
     *
     * <p>The same domain the folds beside it have: a plan is searched at least once, so nothing to
     * join is a caller with no question rather than a question nothing answered.
     */
    @Test
    void noRunsCannotBeJoined() {
        assertThrows(IllegalArgumentException.class, () -> FillResult.acrossRuns(List.of()));
    }

    /**
     * Two plans that are one question are joined, and being one question is a matter of value.
     *
     * <p>The control for the refusal above, and it says which sameness the refusal is about. Held
     * against object identity instead, the runs of a plan a caller had rebuilt would be refused as
     * two questions — and nothing would say so, because a searched behavior hands every run the one
     * plan its obligations were gathered into.
     *
     * <p>Rebuilt around the subject it was asked about rather than read a second time: what a
     * measured input is compares its reading as the capability it is, one per behavior per compile,
     * so two readings are two capabilities and a plan over them is a plan about another compile.
     */
    @Test
    void twoPlansOfOneValueAreOneQuestion() {
        GenerationPlan asked = planOver(List.of(A_CLASS), 1);
        GenerationPlan same = GenerationPlan.of(asked.subject(), asked.classesOwed(),
                asked.armsOwed(), asked.pairsOwed(), asked.meetingsOwed(),
                asked.replacementsOwed(), asked.rewrites());

        assertNotSame(asked, same);
        assertEquals(asked, same);
        assertEquals(new ClassDisposition.Unresolved(NO_CANDIDATE),
                FillResult.acrossRuns(List.of(nothingCameOfIt(asked), nothingCameOfIt(same)))
                        .discharge().at(A_CLASS));
    }

    /**
     * And two runs giving a class the same reason agree, whether or not they say it with the one
     * object.
     *
     * <p>The control for the first refusal. A run makes its own reason out of what its search came
     * to, so two runs that agree agree by what the reasons say.
     */
    @Test
    void twoRunsGivingAClassOneReasonAgree() {
        CameToNothing said = CameToNothing.metNothing(new Generator.UnresolvedCombination(
                List.of("days=low"),
                Generator.UnresolvedCombination.Reason.NO_CANDIDATE_WAS_OFFERED));

        assertNotSame(NO_CANDIDATE, said);
        assertEquals(new ClassDisposition.AcrossRuns.Unresolved(NO_CANDIDATE),
                ClassDisposition.acrossRuns(List.of(
                        new ClassDisposition.Unresolved(NO_CANDIDATE),
                        new ClassDisposition.Unresolved(said))));
    }

    /** The same for two runs reading an arm's places alike, which is the second refusal's control. */
    @Test
    void twoRunsReadingAnArmsPlacesAlikeAgree() {
        ArmDisposition.NoWayIn read = new ArmDisposition.NoWayIn(new PathAccess.Unreachable(
                PathAccess.Unreachable.Why.THE_CONDITION_NEVER_COMES_OUT_THAT_WAY));

        assertNotSame(NOTHING_ARRIVES, read.access().getFirst());
        assertEquals(new ArmDisposition.AcrossRuns.NoWayIn(List.of(NOTHING_ARRIVES)),
                ArmDisposition.acrossRuns(List.of(
                        new ArmDisposition.NoWayIn(NOTHING_ARRIVES), read)));
    }

    /**
     * Runs a figure left unmade are no run beside the ones made: the answer over the ones made
     * says the figure as something it met, in the figure's word. Said as a run of their own, the
     * word would differ from the made runs' and the join would be refused, as above.
     */
    @Test
    void runsAFigureLeftUnmadeAreWhatTheAnswerMetAndNoRunOfTheirOwn() {
        GenerationPlan asked = planOver(List.of(A_CLASS), 1);
        FillResult made = nothingCameOfIt(asked, NO_CANDIDATE);

        CameToNothing came = assertInstanceOf(ClassDisposition.Unresolved.class,
                made.alsoMet(LEFT).discharge().at(A_CLASS)).came();
        assertEquals(Generator.UnresolvedCombination.Reason.wordFor(LEFT), came.why().reason());
        assertEquals(LEFT, came.met().figures(), "and the figure, as met");
        assertEquals(made, made.alsoMet(Set.of()), "nothing left is nothing met");
    }

    /**
     * A class's answer is the one every run gives whatever it stood the dependencies in with, so
     * a proof the runs made gave is the one the runs not made would give, and stands.
     */
    @Test
    void aClassTheRunsMadeProvedIsProvedOverTheRunsNotMade() {
        GenerationPlan asked = planOver(List.of(A_CLASS), 1);
        FillResult made = nothingCameOfIt(asked, PROVED);

        assertEquals(made, made.alsoMet(LEFT));
    }

    /** At a replacement, the figure is said in the words a search for a rewrite says one in. */
    @Test
    void aFigureAtAReplacementIsAFigureOfTheComposing() {
        CompositionBudget figure = CompositionBudget.SEARCHES_A_ROW_IS_COMPOSED_THROUGH;
        assertEquals(new ReplacementDisposition.NoneFound(Map.of(
                        ReplacementDisposition.Ended.A_FIGURE_OF_THE_COMPOSING,
                        ReplacementDisposition.Met.at(Set.of(figure.figure())))),
                FillResult.noneComposedAt(CompositionShortfall.of(Set.of(figure))));
    }

    /** A run of a plan owing one class, which composed nothing for it. */
    private static FillResult nothingCameOfIt(GenerationPlan asked) {
        return nothingCameOfIt(asked, NO_CANDIDATE);
    }

    /** A run of a plan owing one class, which composed nothing for it and said {@code came}. */
    private static FillResult nothingCameOfIt(GenerationPlan asked, CameToNothing came) {
        ClassOfAPosition owed = asked.classesOwed().getFirst();
        return new FillResult(new LinkedHashMap<>(), List.of(), List.of(),
                Discharge.of(asked, List.of(new GenerationAnswer.Class(
                        new GenerationObligation.Class(owed),
                        new ClassDisposition.Unresolved(came)))));
    }

    /**
     * A plan owing the classes given, over a measurement the low class represents with {@code low}.
     *
     * <p>Two plans owing the same classes and dividing the input differently, so that what the
     * runs were asked is the only thing between them. Plans differing in what they owe are refused
     * by the answers not covering the obligations, which is a second reader and not this one.
     */
    private static GenerationPlan planOver(List<ClassOfAPosition> classes, long low) {
        NumericTerm.ValueOf atDays = new NumericTerm.ValueOf(TermPath.of("days"));
        Axis days = new Axis(new AxisId("fee", "days"), atDays,
                List.of(divided("days/low", low).ofTheNumber(atDays),
                        divided("days/high", 9).ofTheNumber(atDays)),
                List.of());
        RuleReadingContext reading =
                RuleReadingContext.unshared(SYMBOLS, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        MeasuredInput subject = MeasuredInput.of("fee",
                InputDomain.of(List.of(new InputDomain.Parameter("days", null, Type.INT)),
                        reading, TypeCardinality.Counts.workedOutIn(reading),
                        Membership.none())
                        .reading(SYMBOLS),
                AxesATestWrote.asAMeasurement("fee", List.of(days)));
        return GenerationPlan.of(subject, classes, List.of(), List.of(), List.of());
    }

    private static PartitionClass divided(String id, long value) {
        return PartitionClass.of(id, id, new Recognition.Nothing(),
                RepresentativeSource.of(List.of(FixtureTemplate.integer(value))));
    }
}
