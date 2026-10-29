package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.Emitted;
import souther.compiler.generated.EvaluationArtifact;
import souther.compiler.generated.MemoryClassLoader;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.observe.ArmObservation;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A fold whose step is chosen as the program runs is recorded as reached once its arguments have
 * been worked out and not before.
 *
 * <p>The loop around it is the same loop as for any fold, so a second element taken is noted. A run
 * that stopped working out the arguments of the fold never entered it: recorded as reached, it
 * would be a row the fold was put to that the fold never saw.
 */
class AWalkRunAsACallIsRecordedOnceItsArgumentsAreWorkedOutTest {

    private static final String MODEL = """
            module example.walked

            behavior total : (flag: Bool, xs: List<Int>) -> Int

            let add (acc: Int, x: Int): Int = acc + x
            let sub (acc: Int, x: Int): Int = acc - x

            let total (flag, xs) = {
                let step = if flag then add else sub
                List.fold(step, 0, List.map(x -> x * 2305843009213693952, xs))
            }
            """;

    @Test
    void aRunThatEntersTheFoldRecordsHowFarItWent() {
        Run run = new Run();

        AlignedObservation one = run.observing(true, List.of(1L));
        AlignedObservation two = run.observing(true, List.of(1L, 1L));

        assertTrue(one.entered(run.fold.index()), "the fold was reached");
        assertFalse(one.wentOn(run.fold.index()), "and a list of one takes no second element");
        assertTrue(two.entered(run.fold.index()));
        assertTrue(two.wentOn(run.fold.index()), "and a list of two does");
    }

    @Test
    void aRunThatStoppedWorkingOutTheArgumentsNeverReachedTheFold() {
        Run run = new Run();

        // Four times a quarter of the largest Int overflows, which aborts the run while the list
        // handed to the fold is being made.
        AlignedObservation stopped = run.stopped(true, List.of(4L));

        assertFalse(stopped.entered(run.fold.index()), "the fold was never called");
    }

    /**
     * A fold works out its arguments in the order they are written, whatever its step is: the seed
     * before the list. What the analyses say of which abort a run reaches first reads that order
     * off the call, so the bytecode keeps it.
     */
    @Test
    void theSeedIsWorkedOutBeforeTheListWhateverTheStepIs() {
        for (String step : List.of("(acc, x) -> acc + x", "if a then add else sub")) {
            Run run = new Run("""
                    module example.walked

                    behavior total : (a: Bool, b: Bool) -> Int

                    let add (acc: Int, x: Int): Int = acc + x
                    let sub (acc: Int, x: Int): Int = acc - x

                    let total (a, b) =
                        List.fold(%s, if a then unreachable "the seed" else 0,
                                  if b then unreachable "the list" else [1])
                    """.formatted(step));

            String message = run.abortMessage(true, true);

            assertTrue(message.contains("the seed"), step + ": " + message);
        }
    }

    /** The classes of the model, loaded, and the fold the author wrote in it. */
    private static final class Run {

        private final CoverageSites.Plan plan;
        private final CoverageSites.WalkSite fold;
        private final Object instance;
        private final Method apply;

        Run() {
            this(MODEL);
        }

        Run(String model) {
            Compilation compilation = Compilation.ofSource(model, "Main");
            compilation.answerEverything();
            Bodies.Elaborated checked = compilation.db()
                    .ask(new Bodies.Checked(compilation.modules().get(0))).value();
            assertNotNull(checked, "the model under test compiles");
            plan = checked.plan();
            List<CoverageSites.WalkSite> written = plan.walks("total").stream()
                    .filter(CoverageSites.WalkSite::writtenHere).toList();
            assertEquals(1, written.size(), () -> "the one fold the model writes: " + plan.walks());
            fold = written.getFirst();
            EvaluationArtifact artifact = compilation.db().ask(new Output.Evaluated(
                    compilation.modules().get(0), ArmObservation.RECORD)).value();
            assertNotNull(artifact, "the model under test compiles");
            Map<String, ClassFileImage> classes = artifact.classes();
            ClassLoader loader = new MemoryClassLoader(classes,
                    AWalkRunAsACallIsRecordedOnceItsArgumentsAreWorkedOutTest.class
                            .getClassLoader());
            try {
                Class<?> impl = Emitted.behavior(loader, "example.walked", "total");
                Constructor<?> ctor = impl.getDeclaredConstructor();
                ctor.setAccessible(true);
                instance = ctor.newInstance();
                apply = Arrays.stream(impl.getDeclaredMethods())
                        .filter(each -> each.getName().equals("apply")).findFirst().orElseThrow();
                apply.setAccessible(true);
            } catch (ReflectiveOperationException e) {
                throw new AssertionError(e);
            }
        }

        AlignedObservation observing(Object... given) {
            Probe.begin(plan.identity());
            try {
                apply.invoke(instance, given);
                return plan.numbering().align(Probe.snapshot());
            } catch (ReflectiveOperationException e) {
                throw new AssertionError(e);
            } finally {
                Probe.end();
            }
        }

        /** What a run recorded that did not come back with an answer. */
        AlignedObservation stopped(Object... given) {
            Probe.begin(plan.identity());
            try {
                InvocationTargetException refused = assertInstanceOf(
                        InvocationTargetException.class,
                        assertThrowsReflective(given), "the run was stopped");
                assertNotNull(refused.getCause());
                return plan.numbering().align(Probe.snapshot());
            } finally {
                Probe.end();
            }
        }

        /** What the run that was stopped said. */
        String abortMessage(Object... given) {
            Probe.begin(plan.identity());
            try {
                InvocationTargetException refused = assertInstanceOf(
                        InvocationTargetException.class,
                        assertThrowsReflective(given), "the run was stopped");
                return String.valueOf(refused.getCause().getMessage());
            } finally {
                Probe.end();
            }
        }

        private Throwable assertThrowsReflective(Object... given) {
            try {
                apply.invoke(instance, given);
            } catch (InvocationTargetException e) {
                return e;
            } catch (ReflectiveOperationException e) {
                throw new AssertionError(e);
            }
            throw new AssertionError("the run was expected to stop");
        }
    }
}
