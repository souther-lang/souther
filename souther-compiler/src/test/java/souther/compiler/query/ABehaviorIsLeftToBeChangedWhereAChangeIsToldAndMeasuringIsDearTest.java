package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.DocumentShape;
import souther.compiler.diag.SourceRendering;
import souther.compiler.observe.Figure;
import souther.compiler.partition.Allowances;
import souther.compiler.partition.BodyReading;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.report.AdequacyReport;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.List;
import java.util.Locale;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior is left unmeasured for its author to change where measuring it stops at a figure in a
 * construct a change is told of, and measured otherwise ({@link ToBeChangedFirst}).
 *
 * <p>What it is left on is what measuring comes to: at each figure the same behavior is left or
 * not as a run that measures it to the end reports it stopped there or not. What the choices
 * multiply to is told of how they are written, and ways no value meets are none of what is asked.
 *
 * <p>And the stop is at what the change is told of. A stop elsewhere in the body is one the change
 * leaves, so the behavior is measured.
 *
 * <p>Asked of the questions and not of a measurement: none is made but to say what a run to the
 * end reports, and by the one test of the report, of a behavior left.
 */
class ABehaviorIsLeftToBeChangedWhereAChangeIsToldAndMeasuringIsDearTest {

    private static final CompositionBudget QUESTIONS =
            CompositionBudget.QUESTIONS_A_STATEMENT_IS_ASKED;

    private static final CompositionBudget READINGS =
            CompositionBudget.TOTAL_READINGS_OF_ONE_CONDITION;

    private static final Allowances ONE_QUESTION = questions(1);

    /** The readings of a condition held to a figure a chain of three choices runs into. */
    private static final Allowances FEW_READINGS = Allowances.DECLARED
            .with(CompositionBudget.READINGS_OF_ONE_CONDITION, 4)
            .with(READINGS, 8);

    private static final String NUMBERS = """
            module m

            let fits (limit: Int, n: Int): Bool = n >= limit

            behavior asked : (limit: Int, a: Int, b: Int) -> Bool
            let asked (limit, a, b) = List.any(n -> fits(limit, n), [ a, b ])
            """;

    private static final String CASES = """
            module m

            data Room = Kitchen | Study

            let fits (wanted: Room, room: Room): Bool = wanted == room

            behavior asked : (wanted: Room) -> Bool
            let asked (wanted) = List.any(room -> fits(wanted, room), [ Kitchen, Study ])
            """;

    /** Whether both numbers are above some threshold: the ways a number is above one and not above
     *  a lower one are counted among the cases, and no number meets them. */
    private static final String THRESHOLDS = """
            module m

            let above (t: Int, x: Int, y: Int): Bool = x > t && y > t

            behavior asked : (x: Int, y: Int) -> Bool
            let asked (x, y) = List.any(t -> above(t, x, y), [ 1, 2, 3 ])
            """;

    /** A chain of choices, each {@code chosen} of the last and an input of its own. */
    private static String chain(String chosen) {
        return """
                module m

                let pick (a: Int, b: Int): Int = %s

                behavior asked : (n0: Int, h0: Int, h1: Int, h2: Int) -> Bool
                let asked (n0, h0, h1, h2) = {
                    let n1 = pick(n0, h0) + 1
                    let n2 = pick(n1, h1) + 1
                    let n3 = pick(n2, h2) + 1
                    n3 == 0
                }
                """.formatted(chosen);
    }

    private static final String CHOICES_THAT_MULTIPLY = chain("if a < b then a else b");

    private static Allowances questions(int figure) {
        return Allowances.DECLARED.with(QUESTIONS, figure);
    }

    private static Compilation leaving(String model, Allowances allowances) {
        Compilation compilation = Compilation.ofSource(model, "Main").allowing(allowances);
        compilation.leaveWhatIsToBeChanged();
        return ACompiledModel.compiles(compilation);
    }

    private static Optional<String> figure(Compilation compilation) {
        return Adequacy.leftToBeChanged(compilation.db(), "m", "asked").figure()
                .map(Figure::name);
    }

    /** Whether a run that measures {@code model} to the end says it stopped at {@code budget}. */
    private static boolean measuredStopsAt(CompositionBudget budget, String model,
                                           Allowances allowances) {
        Compilation compilation = Compilation.ofSource(model, "Main").allowing(allowances);
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.OFF));
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()))
                .contains("(" + budget.name() + ", ");
    }

    @Test
    void aHelperComparingNumbersIsLeftAndOneComparingTheCasesOfASumIsMeasured() {
        assertEquals(Optional.of(QUESTIONS.name()), figure(leaving(NUMBERS, ONE_QUESTION)));

        Compilation cases = leaving(CASES, ONE_QUESTION);
        assertFalse(cases.db().ask(new HelpersReadOnApplicationsAroundThem("m", "asked")).value()
                .isEmpty(), "the same change is told of the helper over cases");
        assertEquals(Optional.empty(), figure(cases));
    }

    @Test
    void aChainOfChoicesIsLeftAndTheSameChainOfChoicesThatComeOutOneWayIsMeasured() {
        assertEquals(Optional.of(READINGS.name()),
                figure(leaving(CHOICES_THAT_MULTIPLY, FEW_READINGS)));

        Compilation oneWay = leaving(chain("if 1 < 2 then a else b"), FEW_READINGS);
        assertTrue(oneWay.db().ask(new ConditionsReadThroughTooManyChoices("m", "asked")).value()
                .conditions() > 0, "the same change is told of the chain that comes out one way");
        assertEquals(Optional.empty(), figure(oneWay));
    }

    /** At the last figure it is left at and at the first it is not, as it is measured there. */
    @Test
    void itIsLeftAtTheFiguresMeasuringItToTheEndStopsAt() {
        int left = 1;
        while (figure(leaving(THRESHOLDS, questions(left * 2))).isPresent()) {
            left *= 2;
        }

        assertEquals(Optional.of(QUESTIONS.name()), figure(leaving(THRESHOLDS, questions(left))));
        assertTrue(measuredStopsAt(QUESTIONS, THRESHOLDS, questions(left)), "at " + left);
        assertFalse(measuredStopsAt(QUESTIONS, THRESHOLDS, questions(left * 2)),
                "at " + left * 2);
    }

    /** The comparison of the body asks more than the helper does, and no change is told of it:
     *  declared as a behavior, the helper leaves what stopped where it was. */
    @Test
    void aBodyThatStopsWhereNothingIsToldOfIsMeasuredThoughAChangeIsToldElsewhere() {
        String elsewhere = """
                module m

                let fits (n: Int): Bool = n >= 1

                behavior asked : (a: Int, b: Int, c: Int, d: Int) -> Bool
                let asked (a, b, c, d) =
                    List.any(n -> fits(n), [ a, b ])
                        && List.any(n -> n >= 5, [ a, b, c, d ])
                """;
        int helper = 1;
        while (figure(leaving(elsewhere, questions(helper))).isPresent()) {
            helper++;
        }

        assertFalse(leaving(elsewhere, questions(helper)).db()
                .ask(new HelpersReadOnApplicationsAroundThem("m", "asked")).value().isEmpty(),
                "a change is told of the helper");
        assertTrue(measuredStopsAt(QUESTIONS, elsewhere, questions(helper)),
                "measuring it stops all the same, at " + helper);
    }

    /** Dear and told of nothing: waiting is the only way to what its rows do not cover. */
    @Test
    void aBehaviorNoChangeIsToldOfIsMeasuredHoweverDear() {
        String inTheBody = NUMBERS.replace("fits(limit, n), [", "n >= limit, [");

        assertTrue(measuredStopsAt(QUESTIONS, inTheBody, ONE_QUESTION));
        assertEquals(Optional.empty(), figure(leaving(inTheBody, ONE_QUESTION)));
    }

    @Test
    void aBehaviorThatStopsAtNoFigureIsMeasuredAndSoIsEveryOneWhereTheBuildDoesNotAsk() {
        assertEquals(Optional.empty(), figure(leaving(NUMBERS, Allowances.DECLARED)));
        assertEquals(Optional.empty(), figure(ACompiledModel.compiles(
                Compilation.ofSource(NUMBERS, "Main").allowing(ONE_QUESTION))));
    }

    /** What is told is what takes it out of the figure's way. */
    @Test
    void changedAsToldNothingIsLeft() {
        assertEquals(Optional.empty(), figure(leaving(
                NUMBERS.replace("let fits (limit: Int, n: Int): Bool = n >= limit", """
                        behavior fits : (limit: Int, n: Int) -> Bool
                        let fits (limit, n) = n >= limit"""), ONE_QUESTION)));
    }

    /** The body is read by no measure of the module, and that of the behavior beside it is. What
     *  arrives where in it is asked only where its conditions are read. */
    @Test
    void theBodyIsReadByNoMeasureAndTheBodyBesideItIs() {
        String beside = """

                behavior beside : (flag: Bool) -> Int
                let beside (flag) = if flag then 1 else 0
                """;
        Db db = leaving(NUMBERS + beside, ONE_QUESTION).db();
        Bodies.Elaborated checked = db.ask(new Bodies.Observable("m")).value();

        assertInstanceOf(BodyReading.ToBeChangedFirst.class,
                Adequacy.bodyReading(db, "m", checked, "asked"));
        assertInstanceOf(BodyReading.Read.class,
                Adequacy.bodyReading(db, "m", checked, "beside"));
        assertEquals(List.of("beside"), List.copyOf(
                db.ask(new Adequacy.DecisionReadings("m")).value().keySet()));
        assertEquals(List.of("beside"), List.copyOf(
                db.ask(new Adequacy.Meets("m")).value().keySet()));
        assertEquals(List.of("beside"), List.copyOf(
                leaving(CHOICES_THAT_MULTIPLY + beside, FEW_READINGS).db()
                        .ask(new Adequacy.PathReached("m")).value().keySet()));
    }

    /** Nothing was shown of its rows, so the verdict is open and no gap is told; what is told is
     *  the figure and the change. */
    @Test
    void theReportSaysWhatToChangeInTheDocumentAndInBothLanguages() {
        Compilation compilation = Compilation.ofSource(NUMBERS, "Main").allowing(ONE_QUESTION);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.leaveWhatIsToBeChanged();
        AdequacyReport report = AdequacyReport.of(ACompiledModel.compiles(compilation));
        SourceRendering rendering = SourceRendering.namedByIdentity(compilation.texts());

        assertEquals(List.of("m.asked"), report.leftToBeChanged());
        assertEquals(AdequacyReport.AdequacyStatus.UNDETERMINED, report.adequacy());
        JsonNode document = JsonMapper.builder().build().readTree(report.json(rendering));
        DocumentShape.assertShapedLikeTheSchema(document);
        JsonNode asked = document.get("modules").get(0).get("behaviors").get(0);
        JsonNode helper = asked.get("toBeChangedFirst").get("helpersAppliedToEachElement").get(0);
        assertEquals("m.fits", helper.get("helper").asString());
        assertEquals(2, helper.get("applicationsAtMost").asInt());
        assertEquals("behavior_to_be_changed_first", asked.get("weakening").get(0).asString());

        String english = report.human(rendering, Locale.ENGLISH);
        assertTrue(english.contains("not measured: as it is written, measuring it stops at"),
                english);
        assertTrue(english.contains("Declared as a behavior, `fits` reads them once"), english);
        String japanese = report.human(rendering, Locale.JAPANESE);
        assertTrue(japanese.contains("測っていない: 今の書き方のまま測ると、途中で上限に達する"), japanese);
        assertTrue(japanese.contains("`fits` を behavior として宣言すると"), japanese);
    }
}
