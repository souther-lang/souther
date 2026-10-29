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
 * A fold run as a call of the library's method, because its step is chosen as the program runs, is
 * recorded as reached once the call is about to be made and not before.
 *
 * <p>Reached is all that is recorded of it. The method is one for every fold of the program, so
 * there is no loop here to note a second element in, and a run that took one has not recorded it.
 * And a run that stopped working out the arguments of the call never made it: recorded as reached,
 * it would be a row the fold was put to that the fold never saw.
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
    void aRunThatMakesTheCallRecordsReachingTheFoldAndNothingOfHowFarItWent() {
        Run run = new Run();

        AlignedObservation one = run.observing(true, List.of(1L));
        AlignedObservation two = run.observing(true, List.of(1L, 1L));

        assertTrue(one.entered(run.fold.index()), "the fold was reached");
        assertTrue(two.entered(run.fold.index()));
        assertFalse(two.wentOn(run.fold.index()), "and no second element is noted of the call");
    }

    @Test
    void aRunThatStoppedWorkingOutTheArgumentsNeverReachedTheFold() {
        Run run = new Run();

        // Four times a quarter of the largest Int overflows, which aborts the run while the list
        // handed to the fold is being made.
        AlignedObservation stopped = run.stopped(true, List.of(4L));

        assertFalse(stopped.entered(run.fold.index()), "the fold was never called");
    }

    /** The classes of the model, loaded, and the fold the author wrote in it. */
    private static final class Run {

        private final CoverageSites.Plan plan;
        private final CoverageSites.WalkSite fold;
        private final Object instance;
        private final Method apply;

        Run() {
            Compilation compilation = Compilation.ofSource(MODEL, "Main");
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
