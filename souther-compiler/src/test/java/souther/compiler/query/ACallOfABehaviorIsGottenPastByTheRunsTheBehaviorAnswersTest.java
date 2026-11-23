package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.DocumentShape;
import souther.compiler.check.CallPassage;
import souther.compiler.check.StopOrigin;
import souther.compiler.diag.SourcePos;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.AStopNotShown;
import souther.compiler.inputs.WhyAStopIsNotShown;
import souther.compiler.meta.ModulePath;
import souther.compiler.report.AdequacyReport;
import souther.compiler.types.TypeKey;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a run stops in a behavior called is asked of the behavior over its own inputs, and where
 * the runs of rows are not shown to get past it, the caller's comparison over the call is not said
 * to be read to the end.
 *
 * <p>No body of a behavior is read where a call of it stands, so a stop in one is nothing a caller
 * reads; it is said by what the behavior answers of itself ({@link Adequacy.RowsRunsGetPast}). The
 * caller's account is settled where the answer is yes, and left open where it is not.
 */
class ACallOfABehaviorIsGottenPastByTheRunsTheBehaviorAnswersTest {

    private static final String NOT_RESOLVED = "stop not resolved";

    /** A caller comparing what `made` answers, each of its two cases expected by a row. */
    private static final String CALLER = """

            data Out = Low | High
            behavior chosen : (n: Int) -> Out
            let chosen (n) = if made(n) >= 5 then Low else High
            example chosen
                | (40) -> Low
                | (2) -> High
            """;

    /** Compiled with no measure asked: what a behavior is told of asks nothing of the rows. */
    private static Compilation compiled(String model) {
        return ACompiledModel.answered("module m\n" + model);
    }

    /** Measured at {@link Adequacy.Level#OFF}: whether a stop is resolved, and why, is what the
     *  rules say, and asks nothing of the rows. */
    private static Compilation readByItsRules(String model) {
        return ACompiledModel.measured("module m\n" + model,
                Adequacy.Asked.reportOnly(Adequacy.Level.OFF));
    }

    /** Measured from the rows: for whether the measurement is complete, which reads them. */
    private static Compilation measured(String model) {
        return ACompiledModel.measured("module m\n" + model,
                Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
    }

    private static String reportOf(Compilation compilation, String behavior) {
        return AdequacyReport.of(compilation).only(null, behavior)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static CallPassage passageOf(Compilation compilation, String behavior) {
        return compilation.db().ask(new Adequacy.RowsRunsGetPast("m", behavior)).value();
    }

    private static boolean rowsRunsGetPast(Compilation compilation, String behavior) {
        return passageOf(compilation, behavior).getsPast();
    }

    /** What {@code behavior} is told of, where it is left open. */
    private static CallPassage.WhyOpen whyOpen(Compilation compilation, String behavior) {
        return assertInstanceOf(CallPassage.Open.class, passageOf(compilation, behavior)).why();
    }

    /** Where in {@code behavior}'s body the proof that a run gets past gave out. */
    private static StopOrigin mayStopAt(Compilation compilation, String behavior) {
        return assertInstanceOf(CallPassage.WhyOpen.MayStopAt.class,
                whyOpen(compilation, behavior)).origin();
    }

    /** The lines of the report that say a stop is not resolved. */
    private static List<String> notResolved(String report) {
        return report.lines().filter(line -> line.contains(NOT_RESOLVED)).toList();
    }

    /** A called behavior whose {@code None} arm is {@code none}, a premise it states, and
     *  {@code scoring} written in place of its {@code Some} arm; a row past twelve only where the
     *  scoring clamps, since a construction of it aborts that row otherwise. */
    private static String throwsScored(String scoring, String none) {
        String pastTwelve = scoring.equals(CLAMPED)
                ? "    | \"13 clamps to twelve\" : (Throw([13])) -> true\n" : "";
        return """
                data Points = Int
                    invariant value >= 0 && value <= 12

                data Throw = List<Int>

                behavior scoreOf : (t: Throw) -> Points

                let scoreOf (t) =
                    match List.get(0, t.value) with
                        | Some n -> %s
                        | None -> %s

                example scoreOf
                    | "pin 5" : (Throw([5])) -> Points(5)
                    | "pin 12" : (Throw([12])) -> Points(12)

                behavior reachedTwelve : (t: Throw) -> Bool

                let reachedTwelve (t) = scoreOf(t).value == 12

                example reachedTwelve
                    | "12 is twelve" : (Throw([12])) -> true
                    | "11 is not" : (Throw([11])) -> false
                %s""".formatted(scoring, none, pastTwelve);
    }

    private static final String CLAMPED = "Points(Int.clamp(0, 12, n))";
    private static final String UNREACHABLE = "unreachable \"a throw always names a pin\"";

    /** An {@code unreachable} is the premise the called behavior states, and its own to account
     *  for: its callers get past it, and their comparison over the call is read to the end. */
    @Test
    void anUnreachableInABehaviorCalledLeavesNoCallerOpen() {
        Compilation compilation = measured(throwsScored(CLAMPED, UNREACHABLE));
        String report = reportOf(compilation, "reachedTwelve");

        assertTrue(rowsRunsGetPast(compilation, "scoreOf"));
        assertTrue(rowsRunsGetPast(compilation, "reachedTwelve"));
        assertEquals(List.of(), notResolved(report), report);
        assertFalse(report.contains("not read: comparison"), report);
        assertTrue(report.contains("measurement: complete"), report);
    }

    /** A construction whose invariant is not shown to hold is no premise anything states: the
     *  caller is left open, and the report names the call and the construction in it. Written
     *  beside an {@code unreachable} in the same body, so taking the premise is shown to take that
     *  and nothing beside it. */
    @Test
    void aConstructionNotShownToHoldInABehaviorCalledIsNamedInTheCallersReport() {
        Compilation compilation = readByItsRules(throwsScored("Points(n)", UNREACHABLE));
        String report = reportOf(compilation, "reachedTwelve");

        assertEquals(new TypeKey("m", "Points"), assertInstanceOf(StopOrigin.AConstruction.class,
                mayStopAt(compilation, "scoreOf")).type());
        List<String> open = notResolved(report);
        assertEquals(1, open.size(), report);
        assertTrue(open.getFirst().contains("a run may stop at the call of scoreOf at "), report);
        assertTrue(open.getFirst().contains("; scoreOf may stop at the construction of Points at "),
                report);
    }

    /** The premise is taken in the body it is written in as by a caller: a comparison over a
     *  value a run works out through an {@code unreachable} is read past it. */
    @Test
    void anUnreachableInTheBodyItIsWrittenInLeavesNoComparisonOpen() {
        Compilation compilation = readByItsRules("""
                data Points = Int
                    invariant value >= 0 && value <= 12
                data Throw = List<Int>
                behavior reachedTwelve : (t: Throw) -> Bool
                let reachedTwelve (t) = {
                    let p = match List.get(0, t.value) with
                        | Some n -> Points(Int.clamp(0, 12, n))
                        | None -> unreachable "a throw always names a pin"
                    p.value == 12
                }
                """);
        String report = reportOf(compilation, "reachedTwelve");

        assertEquals(List.of(), notResolved(report), report);
        assertFalse(report.contains("works out an operation that may end the run"), report);
    }

    /** A stop left untold in a closure the comparison applies says where it is. */
    @Test
    void aStopLeftUntoldInAClosureTheComparisonAppliesIsSaidWhereItIs() {
        Compilation compilation = readByItsRules(throwsScored("Points(n)", "Points(0)") + """

                behavior total : (ts: List<Throw>) -> Bool

                let total (ts) = List.fold((s, t) -> s + scoreOf(t).value, 0, ts) >= 50
                """);
        List<String> open = notResolved(reportOf(compilation, "total"));

        assertFalse(open.isEmpty());
        assertTrue(open.stream().allMatch(line -> line.contains("a run may stop at ")), open::toString);
    }

    /** The premise is taken through every call on the way: of a behavior calling the one that
     *  states it, directly or in the step of a walk. */
    @Test
    void anUnreachableIsTakenThroughEveryCallOnTheWay() {
        Compilation compilation = readByItsRules(throwsScored(CLAMPED, UNREACHABLE) + """

                behavior anyTwelve : (ts: List<Throw>) -> Bool

                let anyTwelve (ts) = List.fold((s, t) -> s || scoreOf(t).value == 12, false, ts)

                example anyTwelve
                    | "one" : ([Throw([5]), Throw([12])]) -> true
                    | "none" : ([Throw([5])]) -> false

                behavior seen : (ts: List<Throw>) -> Int

                let seen (ts) = if anyTwelve(ts) then 1 else 0

                example seen
                    | "one" : ([Throw([12])]) -> 1
                    | "none" : ([]) -> 0
                """);
        String report = reportOf(compilation, "seen");

        assertTrue(rowsRunsGetPast(compilation, "reachedTwelve"));
        assertTrue(rowsRunsGetPast(compilation, "anyTwelve"));
        assertTrue(rowsRunsGetPast(compilation, "seen"));
        assertEquals(List.of(), notResolved(report), report);
    }

    /** Where a call on the way leaves it open, the reason is the one at the end of the calls, and
     *  every call down to it is said. */
    @Test
    void aStopLeftOpenDownACallIsNamedThroughEveryCall() {
        Compilation compilation = readByItsRules(throwsScored("Points(n)", UNREACHABLE) + """

                behavior pinsOf : (t: Throw) -> Int

                let pinsOf (t) = scoreOf(t).value

                behavior twelveOrMore : (t: Throw) -> Bool

                let twelveOrMore (t) = pinsOf(t) >= 12

                example twelveOrMore
                    | "12" : (Throw([12])) -> true
                    | "11" : (Throw([11])) -> false
                """);
        String report = reportOf(compilation, "twelveOrMore");

        StopOrigin.ACall call = assertInstanceOf(StopOrigin.ACall.class,
                mayStopAt(compilation, "pinsOf"));
        assertEquals("scoreOf", call.behavior().name());
        assertInstanceOf(StopOrigin.AConstruction.class,
                assertInstanceOf(CallPassage.WhyOpen.MayStopAt.class,
                        assertInstanceOf(CallPassage.Open.class, call.passage()).why()).origin());
        assertInstanceOf(StopOrigin.ACall.class, mayStopAt(compilation, "twelveOrMore"));
        assertTrue(report.contains("a run may stop at the call of pinsOf at "), report);
        assertTrue(report.contains("; pinsOf may stop at the call of scoreOf at "), report);
        assertTrue(report.contains("; scoreOf may stop at the construction of Points at "), report);
    }

    /** A document says the same: the call, each call down from it, and the construction at the
     *  end, the way the schema shipped beside this says. */
    @Test
    void aDocumentWritesEveryCallDownToWhereThePassageIsLeftOpen() {
        Compilation compilation = readByItsRules(throwsScored("Points(n)", UNREACHABLE) + """

                behavior pinsOf : (t: Throw) -> Int

                let pinsOf (t) = scoreOf(t).value

                behavior twelveOrMore : (t: Throw) -> Bool

                let twelveOrMore (t) = pinsOf(t) >= 12

                example twelveOrMore
                    | "12" : (Throw([12])) -> true
                    | "11" : (Throw([11])) -> false
                """);
        JsonNode document = JsonMapper.builder().build().readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));

        DocumentShape.assertShapedLikeTheSchema(document);
        List<JsonNode> places = document.findValues("restsOn");
        assertTrue(places.stream().anyMatch(place -> place.at("/kind").asString().equals("call")
                && place.at("/module").asString().equals("m")
                && place.at("/behavior").asString().equals("pinsOf")
                && place.at("/passage/reason").asString().equals("may_stop")
                && place.at("/passage/place/behavior").asString().equals("scoreOf")
                && place.at("/passage/place/passage/place/kind").asString()
                        .equals("construction")
                && place.at("/passage/place/passage/place/construction").asString()
                        .equals("m.Points")),
                document::toString);
    }

    /**
     * A behavior called is named in a document by the module that declares it as well as by its
     * name, and a type by its qualified name: two modules may each declare one of a name, and a
     * reader of the document is not left to resolve which.
     */
    @Test
    void aDocumentNamesWhatACallLeavesOpenByTheModuleThatDeclaresIt() {
        String declaring = """
                module %s
                data Points = Int
                    invariant value >= 0 && value <= 12
                behavior calculate : (n: Int) -> Points
                let calculate (n) = Points(n)
                """;
        Compilation compilation = Compilation.ofSources(List.of(
                declaring.formatted("billing"), declaring.formatted("shipping"), """
                        module main
                        import billing ( calculate )
                        behavior twelve : (n: Int) -> Bool
                        let twelve (n) = calculate(n).value == 12
                        """), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.OFF));
        ACompiledModel.compiles(compilation);
        JsonNode document = JsonMapper.builder().build().readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));

        DocumentShape.assertShapedLikeTheSchema(document);
        List<JsonNode> calls = document.findValues("restsOn");
        assertEquals(List.of("billing"), calls.stream()
                .filter(place -> place.at("/behavior").asString().equals("calculate"))
                .map(place -> place.at("/module").asString()).toList(), document::toString);
        assertEquals("billing.Points", calls.getFirst().at("/passage/place/construction")
                .asString(), document::toString);
    }

    private static final String ITEM = "#/$defs/findings/items/properties/unresolved/items";

    /** Whether the schema shipped beside this takes {@code written} at {@code reference}. */
    private static boolean schemaTakes(String written, String reference) {
        return DocumentShape.of(JsonMapper.builder().build().readTree(written), reference)
                .wrong().isEmpty();
    }

    /**
     * The schema holds a stop not resolved to what its reason holds it to here, from one source:
     * for every reason, an operation is written exactly where the reason is of one, and places
     * only where it rests on stops left untold — as the type refuses the rest.
     */
    @Test
    void theSchemaTakesAStopNotResolvedExactlyWhereItsTypeDoes() {
        StopOrigin somewhere = new StopOrigin.SomethingWorkedOut(new SourcePos(0, 0));
        for (WhyAStopIsNotShown why : WhyAStopIsNotShown.values()) {
            for (boolean operation : new boolean[] {false, true}) {
                for (boolean places : new boolean[] {false, true}) {
                    boolean typed;
                    try {
                        new AStopNotShown(operation ? Optional.of("x + 1") : Optional.empty(), why,
                                places ? Optional.of(somewhere) : Optional.empty());
                        typed = true;
                    } catch (IllegalArgumentException refused) {
                        typed = false;
                    }
                    String written = "{\"reason\": \"" + AdequacyReport.word(why) + "\""
                            + (operation ? ", \"operation\": \"x + 1\"" : "")
                            + (places ? ", \"restsOn\": {\"kind\": \"worked_out\"}" : "")
                            + "}";
                    assertEquals(typed, schemaTakes(written, ITEM), written);
                }
            }
        }
    }

    /** And of a place and of a passage, the construction, the call or the place exactly where
     *  what it is names one. */
    @Test
    void theSchemaRefusesAPlaceOrAPassageWithoutWhatItNames() {
        String place = "#/$defs/stopPlace";
        String passage = "#/$defs/passageOfACall";
        String passageOfMade = "\"passage\": {\"reason\": \"may_stop\","
                + " \"place\": {\"kind\": \"worked_out\"}}";
        assertTrue(schemaTakes("{\"kind\": \"call\", \"module\": \"m\", \"behavior\": \"made\", "
                + passageOfMade + "}", place));
        for (String wrong : List.of("{\"kind\": \"construction\"}",
                "{\"kind\": \"worked_out\", \"construction\": \"m.Points\"}",
                "{\"kind\": \"call\", \"module\": \"m\", \"behavior\": \"made\"}",
                "{\"kind\": \"call\", \"behavior\": \"made\", " + passageOfMade + "}",
                "{\"kind\": \"worked_out\", \"module\": \"m\"}",
                "{\"kind\": \"worked_out\", \"behavior\": \"made\"}")) {
            assertFalse(schemaTakes(wrong, place), wrong);
        }
        for (String wrong : List.of("{\"reason\": \"may_stop\"}",
                "{\"reason\": \"no_body\", \"place\": {\"kind\": \"worked_out\"}}")) {
            assertFalse(schemaTakes(wrong, passage), wrong);
        }
    }

    /** Where the proof gives out is asked on the arm it is written on, with what entering the arm
     *  states: a construction on an arm whose condition keeps its invariant is got past. */
    @Test
    void whereAPassageIsLeftOpenIsAskedOnTheArmItIsWrittenOn() {
        Compilation compilation = compiled("""
                data Points = Int
                    invariant value >= 0 && value <= 12
                behavior kept : (n: Int) -> Points
                let kept (n) = if n >= 0 && n <= 12 then Points(n) else Points(0)
                behavior halfKept : (n: Int) -> Points
                let halfKept (n) = if n >= 0 then Points(n) else Points(0)
                """);

        assertTrue(rowsRunsGetPast(compilation, "kept"));
        assertInstanceOf(StopOrigin.AConstruction.class, mayStopAt(compilation, "halfKept"));
    }

    /** Of two calls in one comparison that each leave it open, the one the proof gave out at is
     *  named, and naming it says nothing of the other: neither is taken to be got past. */
    @Test
    void ofTwoCallsThatEachLeaveItOpenNamingOneTakesNeitherAsGotPast() {
        Compilation compilation = readByItsRules("""
                data Out = Low | High
                behavior first : (n: Int) -> Int
                let first (n) = Int.floorMod(100, n)
                behavior second : (n: Int) -> Int
                let second (n) = Int.floorMod(50, n)
                behavior both : (a: Int, b: Int) -> Out
                let both (a, b) = if first(a) + second(b) >= 5 then Low else High
                example both
                    | (40, 40) -> Low
                    | (1, 1) -> High
                """);
        String report = reportOf(compilation, "both");

        assertFalse(rowsRunsGetPast(compilation, "first"));
        assertFalse(rowsRunsGetPast(compilation, "second"));
        assertTrue(report.contains("a run may stop at the call of first at ")
                || report.contains("a run may stop at the call of second at "), report);
    }

    /** What a passage is left open at is said of the behavior's own body: an operation in it, or
     *  that it has none. */
    @Test
    void whatAPassageIsLeftOpenAtIsSaidOfTheBehaviorsOwnBody() {
        Compilation compilation = compiled("""
                behavior made : (n: Int) -> Int
                let made (n) = Int.floorMod(100, n)
                behavior injected : (n: Int) -> Int
                """);

        assertInstanceOf(StopOrigin.SomethingWorkedOut.class, mayStopAt(compilation, "made"));
        assertInstanceOf(CallPassage.WhyOpen.NoBody.class, whyOpen(compilation, "injected"));
    }

    /** A text and a list made one longer stop past what the representation holds alone. The runs
     *  of rows get past that, called as beside the operation itself, and that a run stops there is
     *  said by the body whose operation it is. */
    @Test
    void aStopOfTheRepresentationIsSaidByTheBodyItIsInAndLeavesNoCallerOpen() {
        Compilation compilation = readByItsRules("""
                behavior text : (s: String) -> String
                let text (s) = s ++ "x"
                behavior list : (xs: List<Int>) -> List<Int>
                let list (xs) = xs ++ [1]
                data Out = Low | High
                behavior chosen : (s: String, xs: List<Int>) -> Out
                let chosen (s, xs) =
                    if List.length(list(xs)) >= 3 && String.length(text(s)) >= 3 then Low else High
                """);

        for (String behavior : new String[] {"text", "list"}) {
            assertTrue(rowsRunsGetPast(compilation, behavior), behavior);
            assertTrue(reportOf(compilation, behavior).contains("a run stops only where"), behavior);
        }
        assertFalse(reportOf(compilation, "chosen").contains(NOT_RESOLVED));
    }

    @Test
    void aBehaviorThatMayStopLeavesTheCallersAccountOpen() {
        Compilation compilation = measured("""
                behavior made : (n: Int) -> Int
                let made (n) = Int.floorMod(100, n)
                """ + CALLER);
        String report = reportOf(compilation, "chosen");

        assertFalse(rowsRunsGetPast(compilation, "made"));
        assertFalse(rowsRunsGetPast(compilation, "chosen"), "it calls one that may stop");
        assertTrue(report.contains(NOT_RESOLVED), report);
        assertTrue(report.contains("measurement: partial"), report);
        assertFalse(report.contains("adequacy: satisfied"), report);
    }

    @Test
    void aBehaviorTheRunsOfRowsGetPastLeavesNothingOpen() {
        Compilation compilation = measured("""
                behavior made : (n: Int) -> Int
                let made (n) = if n < 10 then 1 else 20
                """ + CALLER);
        String report = reportOf(compilation, "chosen");

        assertTrue(rowsRunsGetPast(compilation, "made"));
        assertTrue(rowsRunsGetPast(compilation, "chosen"));
        assertFalse(report.contains(NOT_RESOLVED), report);
        assertFalse(report.contains("not accounted for"), report);
        assertTrue(report.contains("measurement: complete"), report);
    }

    /** The inputs it is asked over are the ones it declares, and not what a caller hands it. */
    @Test
    void theInputsItIsAskedOverAreTheBehaviorsOwn() {
        Compilation compilation = compiled("""
                data Divisor = Int
                    invariant value >= 1
                behavior declared : (n: Divisor) -> Int
                let declared (n) = Int.floorMod(100, n.value)
                behavior made : (n: Int) -> Int
                let made (n) = Int.floorMod(100, n)
                behavior chosen : (n: Int) -> Int
                let chosen (n) = made(7) + n
                """);

        assertTrue(rowsRunsGetPast(compilation, "declared"));
        assertFalse(rowsRunsGetPast(compilation, "made"));
        assertFalse(rowsRunsGetPast(compilation, "chosen"));
    }

    /** A value the body builds is asked by its definition, which is run where it is built. */
    @Test
    void aValueTheBodyReadsIsAskedByItsDefinition() {
        Compilation compilation = compiled("""
                let limit: Int = {
                    let half = 3
                    half + half
                }
                behavior made : (n: Int) -> Int
                let made (n) = if n < 3 then limit else n
                let never: Int = {
                    let nought = limit - 6
                    Int.floorMod(100, nought)
                }
                behavior mayStop : (n: Int) -> Int
                let mayStop (n) = if n < 3 then never else n
                """);

        assertTrue(rowsRunsGetPast(compilation, "made"));
        assertFalse(rowsRunsGetPast(compilation, "mayStop"));
    }

    /** A sum past what an `Int` holds ends the run, and one its inputs are declared within does
     *  not: a range the author declares is what shows it. */
    @Test
    void anOperationIsAskedByTheNumbersItsInputsAreDeclaredWithin() {
        Compilation compilation = compiled("""
                data Small = Int
                    invariant value >= 0 && value <= 1000
                behavior ofAny : (a: Int, b: Int) -> Int
                let ofAny (a, b) = a + b
                behavior ofSmall : (a: Small, b: Small) -> Int
                let ofSmall (a, b) = a.value + b.value
                """);

        assertFalse(rowsRunsGetPast(compilation, "ofAny"));
        assertTrue(rowsRunsGetPast(compilation, "ofSmall"));
    }

    /** One with no body in the model is not known to answer, called or injected. */
    @Test
    void aBehaviorWithNoBodyIsNotKnownToAnswer() {
        Compilation compilation = readByItsRules("""
                data Out = Low | High
                behavior made : (n: Int) -> Int
                behavior chosen : (n: Int) -> Out
                    depends on made
                let chosen (n, made) = if made(n) >= 5 then Low else High
                """);

        assertFalse(rowsRunsGetPast(compilation, "made"));
        assertFalse(rowsRunsGetPast(compilation, "chosen"));
        assertTrue(reportOf(compilation, "chosen").contains(NOT_RESOLVED));
    }

    /** One behavior called on several inputs is one answer about itself: each comparison over a
     *  call of it is left open, or none is. */
    @Test
    void aBehaviorCalledOnSeveralInputsIsOneAnswer() {
        Compilation compilation = readByItsRules("""
                data Out = Low | High
                behavior made : (n: Int) -> Int
                let made (n) = Int.floorMod(100, n)
                behavior twice : (a: Int, b: Int) -> Out
                let twice (a, b) = if made(a) >= 5 && made(b) >= 5 then Low else High
                example twice
                    | (40, 40) -> Low
                    | (40, 2) -> High
                """);
        String report = reportOf(compilation, "twice");

        assertEquals(2, notResolved(report).size(), report);
    }

    /** A measured caller reads it though the build does not measure the behavior called. */
    @Test
    void itIsAskedOfABehaviorTheBuildDoesNotMeasure() {
        Compilation compilation = Compilation.ofSource("""
                module m
                behavior made : (n: Int) -> Int
                let made (n) = if n < 10 then 1 else 20
                """ + CALLER, "Main");
        compilation.choose(new Adequacy.Choice(null, "chosen"));
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.OFF));
        ACompiledModel.compiles(compilation);

        String report = reportOf(compilation, "chosen");
        assertFalse(report.contains(NOT_RESOLVED), report);
    }
}
