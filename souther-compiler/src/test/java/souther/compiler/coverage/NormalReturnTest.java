package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether an expression can answer a value.
 *
 * <p>The question the arm measure and the exclusion facts both rest on, asked here on its own. It is
 * about evaluation and not about control structures alone: an expression aborts if anything it has to
 * evaluate first aborts, so a value built out of an {@code unreachable} answers as little as the
 * {@code unreachable} itself.
 */
class NormalReturnTest {

    private static final String TYPES = """
            module example.probe

            data On
            data Off
            data Flag = On | Off
            data Answer = Int
            data Boxed = { n: Answer }

            behavior pick : (f: Flag, senior: Bool) -> Answer
            """;

    /** A body that builds nothing, so the signature declares no construction. */
    private static boolean answers(String body) {
        return answersIn(TYPES + "\n" + body);
    }

    private static boolean answersConstructing(String body) {
        return answersIn(TYPES + "    constructs Answer\n\n" + body);
    }

    private static boolean answersBoxing(String body) {
        return answersIn(TYPES + "    constructs Answer, Boxed\n\n" + body);
    }

    private static boolean answersIn(String source) {
        return NormalReturn.of(bodyOf(source, "pick"));
    }

    private static Core bodyOf(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        Bodies.Elaborated checked = compilation.db()
                .ask(new Bodies.Checked(compilation.modules().get(0))).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get(behavior);
        assertNotNull(body, "the behavior under test has a body");
        return body;
    }

    @Test
    void aValueAnswers() {
        assertTrue(answersConstructing("let pick (f, senior) = Answer(1)"));
    }

    @Test
    void anUnreachableAnswersNothing() {
        assertFalse(answers("""
                let pick (f, senior) = unreachable "the probe is never applied"
                """));
    }

    /** A fork answers where a path out of it answers, and not where every path aborts. */
    @Test
    void aMatchAnswersWhereOneArmDoes() {
        assertTrue(answersConstructing("""
                let pick (f, senior) = match f with
                    | On  -> Answer(1)
                    | Off -> unreachable "only On is passed"
                """));
        assertFalse(answers("""
                let pick (f, senior) = match f with
                    | On  -> unreachable "not On"
                    | Off -> unreachable "nor Off"
                """));
    }

    @Test
    void anIfAnswersWhereOneArmDoes() {
        assertTrue(answersConstructing("""
                let pick (f, senior) =
                    if senior then Answer(1) else unreachable "only a senior is passed"
                """));
        assertFalse(answers("""
                let pick (f, senior) =
                    if senior then unreachable "not senior" else unreachable "nor junior"
                """));
    }

    /**
     * A construction evaluates what it is made of, so a field built from an {@code unreachable}
     * leaves the construction with nothing to answer.
     *
     * <p>This is the case a rule written over control structures alone gets wrong: there is no fork
     * here, and the arm that held this would still be counted as one a row can be in.
     */
    @Test
    void aValueBuiltOutOfAnUnreachableAnswersNothing() {
        assertFalse(answersBoxing("""
                let pick (f, senior) = Boxed { n = Answer(unreachable "no number to give") }.n
                """));
        assertTrue(answersBoxing("""
                let pick (f, senior) = Boxed { n = Answer(1) }.n
                """));
    }

    /**
     * A function handed to a call is made here and run there.
     *
     * <p>Evaluating this position produces the function; whether its body aborts is decided when the
     * call gets round to applying it, and on an argument this position does not have. A step that
     * aborts on an element it may never be handed does not stop the expression around it from
     * answering — read the other way, a class rows really do sit in leaves the denominator.
     */
    @Test
    void aFunctionPassedToACallIsMadeAndNotRun() {
        Core tally = bodyOf("""
                module example.higher

                data Answer = Int

                behavior tally : (xs: List<Int>) -> Answer
                    constructs Answer

                let tally (xs) =
                    Answer(List.fold((acc, x) -> Answer(unreachable "no element arrives").value,
                                     0, xs))
                """, "tally");

        assertTrue(NormalReturn.of(tally));
    }

    /** A binding's value is evaluated before the body that reads it. */
    @Test
    void aBindingWhoseValueAbortsStopsTheBody() {
        assertFalse(answersConstructing("""
                let pick (f, senior) = {
                    let n: Int = unreachable "no number to give"
                    Answer(n)
                }
                """));
    }
}
