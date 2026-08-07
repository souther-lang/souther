package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.observe.InputCaseEvidence;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.GeneratedRows;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A model that says where it has no answer, measured against what it can be asked.
 *
 * <p>Reaching an {@code unreachable} is E1911, so a case behind one is a case no row may be written
 * at. Counted in, it is a gap that stays open however the model is exercised — and the model that
 * invents a fallback answer instead reports full coverage, so the report pays for the wrong one.
 *
 * <p>Three measures asked for that row, each deriving what there was to cover on its own. They are
 * measured together here for that reason: what the signature counts, what a position is divided into
 * and what the generator offers are one universe, and a test that fixed one of them would leave the
 * other two free to disagree with it again.
 */
class ACaseTheModelRulesOutIsNotOwedARowTest {

    /** {@code Pending} is a case with an answer and no row: a gap that is real, beside one that is
     * not. Without it, a measure that simply reported nothing would pass every assertion here. */
    private static final String MODEL = """
            module example.probe

            data On
            data Off
            data Pending
            data Flag = On | Off | Pending
            data Answer = Int

            behavior pick : (f: Flag) -> Answer
                constructs Answer

            let pick (f) = match f with
                | On      -> Answer(1)
                | Pending -> Answer(0)
                | Off     -> unreachable "the probe never passes Off"

            example pick
                | "on" : (On) -> Answer(1)
            """;

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return compilation;
    }

    private static InputCaseEvidence input(String source, int at) {
        Compilation compilation = measured(source);
        Adequacy.SignatureEvidence signature = compilation.db()
                .ask(new Adequacy.Witnesses(compilation.modules().get(0))).value().get("pick");
        assertNotNull(signature, "the model under test compiles");
        return signature.inputs().get(at);
    }

    private static PartitionEvidence.AxisCoverage axis(String source) {
        return axis(source, "f");
    }

    private static PartitionEvidence.AxisCoverage axis(String source, String path) {
        Compilation compilation = measured(source);
        PartitionEvidence partition = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value().get("pick");
        assertNotNull(partition, "the model under test compiles");
        return partition.axes().stream().filter(each -> each.path().equals(path))
                .findFirst().orElseThrow();
    }

    /**
     * The identity the three measures share.
     *
     * <p>A case stays declared — the type has it, and that is part of what the model says — and leaves
     * what the rows are held to. Asserting the arithmetic rather than the two numbers separately, so
     * that a case going missing from both sides at once cannot pass.
     */
    @Test
    void whatIsDeclaredIsWhatIsCoverableAndWhatIsRuledOut() {
        InputCaseEvidence input = input(MODEL, 0);

        assertEquals(3, input.declared().size());
        assertEquals(1, input.excluded().size());
        assertEquals(input.declared().size(),
                input.coverable().size() + input.excluded().size());
        assertEquals(List.of("Off"), input.excluded().stream().map(each -> each.name()).toList());
    }

    /** The gap that is real is still reported; the one no row can fill is not. */
    @Test
    void theCaseWithAnAnswerIsStillOwedARow() {
        assertEquals(List.of("Pending"),
                input(MODEL, 0).unspecified().stream().map(each -> each.name()).toList());
    }

    @Test
    void thePositionIsDividedIntoWhatARowCanBeWrittenAt() {
        PartitionEvidence.AxisCoverage axis = axis(MODEL);

        assertEquals(List.of("On", "Pending"), axis.classes());
        assertEquals(List.of("Pending"), axis.uncovered());
        assertEquals(List.of("Off"),
                axis.excluded().stream().map(PartitionEvidence.ExcludedClass::classId).toList());
    }

    /** The model's own words, kept: what a report takes out of a denominator it has to be able to say
     * it took out, and why. */
    @Test
    void whyItIsRuledOutIsTheReasonTheModelWrote() {
        assertEquals(List.of("the probe never passes Off"),
                axis(MODEL).excluded().get(0).reasons());
    }

    /**
     * The reasons on the path that aborts, and nothing written past where it stops.
     *
     * <p>A construction whose first field aborts never evaluates the second, so a second
     * {@code unreachable} below it is text that never runs rather than a reason the value did not
     * arrive. Which one is first is the order the fields are declared and not the order the
     * initializers are written — the emitter walks the declaration and picks each field's
     * initializer out — so the two are written against each other here. Paths a fork keeps apart are
     * another matter: each of them is a way this arm answers nothing, so each is named.
     */
    @Test
    void theReasonsAreTheOnesEvaluationReaches() {
        String sequential = """
                module example.probe

                data On
                data Off
                data Flag = On | Off
                data Answer = Int
                data Boxed = { a: Answer, b: Answer }

                behavior pick : (f: Flag) -> Answer
                    constructs Answer, Boxed

                let pick (f) = match f with
                    | On  -> Answer(1)
                    | Off -> Boxed { b = unreachable "written first and evaluated second"
                                   , a = unreachable "declared first, so this is where it stops"
                                   }.a

                example pick
                    | "on" : (On) -> Answer(1)
                """;

        assertEquals(List.of("declared first, so this is where it stops"),
                axis(sequential).excluded().get(0).reasons());

        String forked = """
                module example.probe

                data On
                data Off
                data Flag = On | Off
                data Yes
                data No
                data Mark = Yes | No
                data Answer = Int

                behavior pick : (f: Flag, m: Mark) -> Answer
                    constructs Answer

                let pick (f, m) = match f with
                    | On  -> Answer(1)
                    | Off -> match m with
                                 | Yes -> unreachable "not a marked Off"
                                 | No  -> unreachable "nor an unmarked one"

                example pick
                    | "on" : (On, Yes) -> Answer(1)
                """;

        assertEquals(List.of("not a marked Off", "nor an unmarked one"),
                axis(forked).excluded().get(0).reasons(),
                "both arms are ways this arm answers nothing");
    }

    /**
     * A warning an author cannot act on is worse than no warning.
     *
     * <p>E1915 asks for a row at an input case and E1918 for a row through an arm. Both are warned
     * about here and both are about {@code Pending}, which is a row that can be written; neither is
     * about {@code Off}, which is not.
     */
    @Test
    void nothingIsWarnedAboutThatNoRowCouldAnswer() {
        assertEquals(List.of("E1915", "E1918"), warnings(MODEL).stream().sorted().toList());
        assertTrue(messages(MODEL).stream().allMatch(said -> said.contains("Pending")),
                messages(MODEL).toString());
        assertFalse(messages(MODEL).stream().anyMatch(said -> said.contains("Off")),
                messages(MODEL).toString());
    }

    private static List<String> warnings(String source) {
        return reported(source).stream().map(d -> d.code()).toList();
    }

    /** What each warning is about, read off its arguments: the rendered text is the catalog's and
     * this is about which case was named. */
    private static List<String> messages(String source) {
        return reported(source).stream()
                .map(d -> java.util.Arrays.stream(d.args()).map(String::valueOf)
                        .collect(java.util.stream.Collectors.joining(" ")))
                .toList();
    }

    private static List<Diagnostic> reported(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        compilation.answerEverything();
        List<Diagnostic> out = new ArrayList<>();
        for (Db.Found found : compilation.db().allReports()) {
            Diagnostic d = found.report().diagnostic();
            if (!found.report().isError() && d.code() != null && d.code().startsWith("E19")) {
                out.add(d);
            }
        }
        return out;
    }

    /**
     * What the generator offers has to be what the compiler accepts.
     *
     * <p>The row it used to write for {@code Off} was E1911 the moment it was uncommented: the tool
     * handing an author work its own compiler refuses. Checked by writing the rows out, answering
     * them and compiling — a generator that offered nothing at all would pass an assertion about
     * {@code Off} alone, so what it does offer is fixed as well.
     */
    @Test
    void everyRowTheGeneratorOffersCompiles() {
        String offered = GeneratedRows.of(measured(MODEL), "example.probe", "pick", false);

        assertTrue(offered.contains("(Pending)"), offered);
        assertFalse(offered.contains("(Off)"), offered);

        String answered = MODEL + "\n" + uncommented(offered).replace("<?>", "Answer(0)");
        Compilation amended = Compilation.ofSource(answered, "Main");
        amended.answerEverything();
        assertEquals(List.of(), amended.db().allReports().stream()
                .filter(found -> found.report().isError())
                .map(found -> found.report().diagnostic().code()).toList(), answered);
    }

    /** The rows out of a generated block, with the comment marker each is offered behind removed. */
    private static String uncommented(String offered) {
        StringBuilder out = new StringBuilder();
        for (String line : offered.split("\n")) {
            if (line.startsWith("// example") || line.startsWith("//     |")) {
                out.append(line.substring(3)).append('\n');
            }
        }
        return out.toString();
    }

    /**
     * A step handed to a combinator is not the arm running it.
     *
     * <p>Evaluating the position a function is written in makes the function; its body runs when the
     * call applies it, on arguments this position does not have — a step that aborts on an element it
     * may never be handed is not the arm failing to answer. Read the other way round, the arm holding
     * the call is not an arm, and the case in front of it leaves the denominator: a class rows do sit
     * in, and here a row sits in it.
     *
     * <p>Checked through the measures rather than on the predicate alone, because what the mistake
     * costs is downstream of it: the row for {@code Off} is written, runs and holds, and the report
     * used to say the position had one class and two rows specified at it.
     */
    @Test
    void aStepThatAbortsDoesNotRuleOutTheCaseThatPassesItAlong() {
        String higher = """
                module example.probe

                data On
                data Off
                data Flag = On | Off
                data Answer = Int

                behavior pick : (f: Flag, xs: List<Int>) -> Answer
                    constructs Answer

                let pick (f, xs) = match f with
                    | On  -> Answer(1)
                    | Off -> Answer(List.fold(
                                 (acc, x) -> Answer(unreachable "no element arrives").value, 0, xs))

                example pick
                    | "on"  : (On, [1]) -> Answer(1)
                    | "off" : (Off, []) -> Answer(0)
                """;

        assertEquals(List.of(), input(higher, 0).excluded().stream().toList());
        assertEquals(2, input(higher, 0).coverable().size());
        assertEquals(List.of(), input(higher, 0).unspecified().stream().toList());
        assertEquals(List.of("On", "Off"), axis(higher).classes());
        assertEquals(List.of(), axis(higher).uncovered());
    }

    /**
     * A binding before the fork does not hide it.
     *
     * <p>What a {@code let} binds is evaluated on the way to the answer and is not a fork, so the
     * {@code match} below it is still the first fork this body has.
     */
    @Test
    void aBindingBeforeTheForkIsSteppedOver() {
        String bound = """
                module example.probe

                data On
                data Off
                data Flag = On | Off
                data Answer = Int

                behavior pick : (f: Flag) -> Answer
                    constructs Answer

                let pick (f) = {
                    let one = 1
                    match f with
                        | On  -> Answer(one)
                        | Off -> unreachable "the probe never passes Off"
                }

                example pick
                    | "on" : (On) -> Answer(1)
                """;

        assertEquals(List.of("Off"),
                input(bound, 0).excluded().stream().map(each -> each.name()).toList());
    }

    /**
     * Nothing is read off a condition.
     *
     * <p>Which values satisfy a predicate is what a solver answers, and a wrong answer here takes a
     * case out of the report that an author should have been asked about. The case stays in, and the
     * gap it leaves is reported as the gap it is.
     */
    @Test
    void aCaseRuledOutByAConditionIsNotReadAsRuledOut() {
        String guarded = """
                module example.probe

                data On
                data Off
                data Flag = On | Off
                data Answer = Int

                behavior pick : (f: Flag, senior: Bool) -> Answer
                    constructs Answer

                let pick (f, senior) =
                    if senior then unreachable "no senior reaches this" else Answer(1)

                example pick
                    | "on" : (On, false) -> Answer(1)
                """;

        assertEquals(List.of(), input(guarded, 0).excluded().stream().toList());
        assertEquals(List.of("Off"),
                input(guarded, 0).unspecified().stream().map(each -> each.name()).toList());
    }

    /**
     * An exclusion under a fork is not lifted out of it.
     *
     * <p>An arm of one {@code match} holding a {@code match} on another parameter says what that
     * parameter cannot be <em>given the first one</em>. Read as a fact about the parameter it would
     * remove a case that other arms do answer for.
     */
    @Test
    void anExclusionThatHoldsOnlyUnderAnotherCaseIsNotReadAsHoldingEverywhere() {
        String nested = """
                module example.probe

                data On
                data Off
                data Flag = On | Off
                data Yes
                data No
                data Mark = Yes | No
                data Answer = Int

                behavior pick : (f: Flag, m: Mark) -> Answer
                    constructs Answer

                let pick (f, m) = match f with
                    | On  -> match m with
                                 | Yes -> Answer(1)
                                 | No  -> unreachable "no unmarked On arrives"
                    | Off -> Answer(0)

                example pick
                    | "on" : (On, Yes) -> Answer(1)
                """;

        assertEquals(List.of(), input(nested, 1).excluded().stream().toList(),
                "`No` is answered when `f` is `Off`");
        assertEquals(List.of("No"),
                input(nested, 1).unspecified().stream().map(each -> each.name()).toList());
    }

    /** And the arm inside is still not an arm: what the body does not answer for is not a fork a row
     * takes, wherever it is written. */
    @Test
    void theArmUnderTheForkIsStillNotAnArm() {
        CompileException refused = org.junit.jupiter.api.Assertions.assertThrows(
                CompileException.class, () -> Compiler.compile(MODEL + """

                        example pick
                            | "off" : (Off) -> Answer(0)
                        """));

        assertEquals("E1911", refused.diagnostics().get(0).code(), refused.getMessage());
    }
}
