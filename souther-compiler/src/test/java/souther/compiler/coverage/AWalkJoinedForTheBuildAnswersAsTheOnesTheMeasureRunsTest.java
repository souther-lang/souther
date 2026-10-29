package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.Compiler;
import souther.compiler.Emitted;
import souther.compiler.generated.EvaluationArtifact;
import souther.compiler.generated.MemoryClassLoader;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.observe.ArmObservation;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Walks the emitter joins into one loop answer what they answer as separate loops, for every list.
 *
 * <p>The classes that record a run keep each walk the source wrote a loop of its own, so that a
 * rewrite of one is a rewrite of that one; the classes a program is built into join them. What is
 * measured is then not the loop that runs, and the only thing that makes that fair is that the join
 * changes when each step runs and not what the walk answers. Held here, over the lists a join could
 * tell apart: nothing, one element the first step drops, one it keeps, and orders of both.
 */
class AWalkJoinedForTheBuildAnswersAsTheOnesTheMeasureRunsTest {

    private static final String MODEL = """
            module example.chain

            behavior kept : (xs: List<Int>) -> List<Int>
            behavior keptTwice : (xs: List<Int>) -> List<Int>
            behavior counted : (xs: List<Int>) -> Int

            let kept (xs) = List.map(x -> x * 2, List.filter(x -> x > 1, xs))

            let keptTwice (xs) =
                List.map(x -> x + 1, List.map(x -> x * 2, List.filter(x -> x > 1, xs)))

            let counted (xs) = {
                let ys = List.filter(x -> x > 1, xs)
                List.length(List.map(x -> x * 3, ys))
            }
            """;

    private static final List<List<Long>> INPUTS = List.of(
            List.of(), List.of(1L), List.of(2L), List.of(1L, 2L), List.of(2L, 1L),
            List.of(3L, 1L, 4L, 1L, 5L), List.of(1L, 1L), List.of(7L, 8L, 9L));

    @Test
    void theClassesThatRecordAndTheOnesABuildIsMadeOfAnswerAlike() throws Exception {
        Map<String, ClassFileImage> built = Compiler.compile(MODEL);
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        EvaluationArtifact measured = compilation.db().ask(new Output.Evaluated(
                compilation.modules().get(0), ArmObservation.RECORD)).value();
        assertNotNull(measured, "the model under test compiles");

        for (String behavior : List.of("kept", "keptTwice", "counted")) {
            Method joined = apply(built, behavior);
            Method apart = apply(measured.classes(), behavior);
            for (List<Long> xs : INPUTS) {
                assertEquals(answer(apart, behavior, xs), answer(joined, behavior, xs),
                        behavior + " " + xs);
            }
        }
    }

    private Object answer(Method apply, String behavior, List<Long> xs) throws Exception {
        try {
            return apply.invoke(instances.get(apply), xs);
        } catch (InvocationTargetException e) {
            throw new AssertionError(behavior + " " + xs, e.getCause());
        }
    }

    private final Map<Method, Object> instances = new IdentityHashMap<>();

    private Method apply(Map<String, ClassFileImage> classes, String behavior)
            throws ReflectiveOperationException {
        ClassLoader loader = new MemoryClassLoader(classes,
                AWalkJoinedForTheBuildAnswersAsTheOnesTheMeasureRunsTest.class.getClassLoader());
        Class<?> impl = Emitted.behavior(loader, "example.chain", behavior);
        Constructor<?> ctor = impl.getDeclaredConstructor();
        ctor.setAccessible(true);
        Method apply = Arrays.stream(impl.getDeclaredMethods())
                .filter(each -> each.getName().equals("apply")).findFirst().orElseThrow();
        apply.setAccessible(true);
        instances.put(apply, ctor.newInstance());
        return apply;
    }
}
