package souther.compiler.coverage;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.Emitted;
import souther.compiler.generated.EvaluationArtifact;
import souther.compiler.generated.MemoryClassLoader;
import souther.compiler.observe.ArmObservation;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;

import java.lang.reflect.Constructor;
import java.lang.reflect.Method;
import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value emitted as a method of its own records the places of its body when a run goes through it.
 *
 * <p>The plan numbers a value's comparisons and arms as places of the module, owed by every behavior
 * that calls the value. Those numbers have to be written into the method the value runs as, or the
 * generation is refused for planning places nothing emitted. This is asked of the classes by running
 * them: a run through {@code f} reaches {@code bigger}, which reads {@code big}, and both values'
 * places have to come back. So do the places of a lambda in a value — one the value's body applies
 * itself, and one it hands on as a function that {@code f} applies.
 *
 * <p>The helper is the control on the other side. It is emitted on the same class as the values and
 * is no body the plan numbers, so its fork has to be emitted without a probe.
 */
class AValuesPlacesAreRecordedWhereItsMethodRunsTest {

    private static final String MODULE = "example.shared";

    private static final String MODEL = """
            module example.shared

            let big = if List.length([1, 2, 3]) > 2 then 1 else 0

            let bigger = if big > 0 then 2 else 3

            let picked = List.filter(x -> x > 1, [1, 2, 3])

            let steps: List<(Int) -> Int> = [x -> if x > 1 then 1 else 0]

            partial let countdown (k: Int): Int = if k <= 0 then 0 else countdown(k - 1)

            behavior f : (n: Int) -> Int
            let f (n) = if n > 0
                then bigger + List.length(picked) + List.sum(List.map(s -> s(n), steps))
                    + countdown(n)
                else 0
            """;

    @Test
    void aRunThroughAValueRecordsThePlacesOfItsBody() {
        Compilation compilation = Compiler.compiled(MODEL, "Main");
        CoverageSites.Plan plan = compilation.db()
                .ask(new Bodies.Checked(MODULE)).value().plan();
        EvaluationArtifact artifact = compilation.db()
                .ask(new Output.Evaluated(MODULE, ArmObservation.RECORD)).value();
        assertNotNull(artifact, "the model compiles measured");

        Set<Integer> recorded = recordedFor(artifact, plan.identity(), 1L);

        // `steps` forks inside a function it hands on, so its fork is run where `f` calls it.
        for (String value : new String[] {"big", "bigger", "steps"}) {
            Set<Integer> comparisons = new LinkedHashSet<>();
            Set<Integer> arms = new LinkedHashSet<>();
            for (CoverageSites.Site site : plan.sites()) {
                if (site.body().equals(value)) {
                    (site instanceof CoverageSites.ComparisonSite ? comparisons : arms)
                            .add(site.index().raw());
                }
            }
            assertFalse(comparisons.isEmpty(), "`" + value + "` is numbered a comparison");
            assertEquals(2, arms.size(), "`" + value + "` is numbered both arms of its fork");
            assertTrue(recorded.containsAll(comparisons),
                    "the comparison of `" + value + "` is recorded: " + recorded);
            // Each fork comes out one way on this run, so one arm of the two is reached.
            assertEquals(1, arms.stream().filter(recorded::contains).count(),
                    "one arm of `" + value + "` is recorded: " + recorded);
        }
        // A comparison in a lambda the value's own body applies is still the value's.
        Set<Integer> inTheLambda = new LinkedHashSet<>();
        for (CoverageSites.Site site : plan.sites()) {
            if (site.body().equals("picked") && site instanceof CoverageSites.ComparisonSite) {
                inTheLambda.add(site.index().raw());
            }
        }
        assertFalse(inTheLambda.isEmpty(), "`picked` is numbered the comparison in its lambda");
        assertTrue(recorded.containsAll(inTheLambda),
                "the comparison in `picked`'s lambda is recorded: " + recorded);
    }

    /** Every place the one run reached, arms and comparisons together. */
    private static Set<Integer> recordedFor(EvaluationArtifact artifact, NumberingIdentity under,
                                            long n) {
        ClassLoader loader = new MemoryClassLoader(artifact.classes(),
                AValuesPlacesAreRecordedWhereItsMethodRunsTest.class.getClassLoader());
        Probe.begin(under);
        try {
            Class<?> impl = Emitted.behavior(loader, MODULE, "f");
            Constructor<?> ctor = impl.getDeclaredConstructor();
            ctor.setAccessible(true);
            Method apply = impl.getDeclaredMethod("apply", Object.class);
            apply.setAccessible(true);
            apply.invoke(ctor.newInstance(), n);
            Observation seen = Probe.snapshot();
            Set<Integer> out = new LinkedHashSet<>(seen.arms());
            seen.outcomes().forEach(way -> out.add(way.at()));
            return out;
        } catch (ReflectiveOperationException e) {
            throw new AssertionError(e);
        } finally {
            Probe.end();
        }
    }
}
