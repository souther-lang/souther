package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.examples.MemoryClassLoader;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;

import java.lang.classfile.ClassFile;
import java.lang.classfile.constantpool.ClassEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.lang.reflect.Constructor;
import java.lang.reflect.Method;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.Executors;
import java.util.concurrent.ExecutorService;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Classes generated to record where a run went, and classes generated to ship.
 *
 * <p>Two claims are being held to, and they pull against each other. The measured classes have to
 * record the arms a run actually takes, which is asked by running them and reading what comes back.
 * And the shipped classes have to have no idea any of this exists: a jar that mentioned {@code Probe}
 * would resolve it nowhere the compiler is absent, which is every machine a Souther program runs on.
 */
class ProbedBytecodeTest {

    /** Four arms: two guards, each with a departure. Inputs are bare numbers so that driving the
     * generated class needs no value built by hand — what is under test is the arms, not the decoder. */
    private static final String MODEL = """
            module example.trip

            data Submitted = { cost: Int }
            data Waiting = { cost: Int }

            behavior submit : (cost: Int) -> Submitted | Waiting
                constructs Submitted, Waiting

            let submit (cost) = {
                guard cost >= 0 else Waiting { cost = 0 }
                guard cost <= 100 else Waiting { cost = cost }
                Submitted { cost = cost }
            }
            """;

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        return compilation;
    }

    private static Map<String, byte[]> probed(Compilation compilation) {
        Map<String, byte[]> classes = compilation.db()
                .ask(new Output.Evaluated(compilation.modules().get(0),
                        Output.CoverageMode.ARMS)).value();
        assertNotNull(classes, "the model under test compiles");
        return classes;
    }

    /** The classes a class names — what a loader will go looking for when it loads this one. */
    private static Set<String> referencedClasses(byte[] bytes) {
        Set<String> names = new LinkedHashSet<>();
        for (PoolEntry entry : ClassFile.of().parse(bytes).constantPool()) {
            if (entry instanceof ClassEntry cls) {
                names.add(cls.asInternalName());
            }
        }
        return names;
    }

    private static final String PROBE = "souther/compiler/coverage/Probe";

    // --- what the measured classes record --------------------------------------------------------

    /**
     * The arms a run takes, read off a run.
     *
     * <p>Three inputs, each going a different way through the two guards. Each has to come back with a
     * different set, and between them they have to reach every site the plan numbered — the arms and
     * the comparisons of the guards' conditions — which is what makes this about what was recorded
     * and not about three calls that happened to return.
     */
    @Test
    void aRunRecordsTheArmsItTook() {
        Compilation compilation = compiled();
        CoverageSites.Plan plan =
                Output.Evaluated.planOf(compilation.db(), compilation.modules().get(0));
        Behavior submit = new Behavior(probed(compilation));

        Set<Integer> negative = submit.armsFor(-1L);
        Set<Integer> cheap = submit.armsFor(50L);
        Set<Integer> dear = submit.armsFor(500L);

        assertNotEquals(negative, cheap);
        assertNotEquals(cheap, dear);
        assertNotEquals(negative, dear);
        Set<Integer> between = new LinkedHashSet<>(negative);
        between.addAll(cheap);
        between.addAll(dear);
        assertEquals(plan.sites().size(), between.size(),
                "between them the three rows reach every site the plan numbered");
    }

    /** A hit belongs to the thread that made it. Rows are evaluated on their own workers, and a set
     * shared between them would put every row's arms on every row. */
    @Test
    void oneThreadsArmsAreNotAnothers() throws Exception {
        Behavior submit = new Behavior(probed(compiled()));
        ExecutorService elsewhere = Executors.newSingleThreadExecutor();
        try {
            Probe.begin();
            submit.apply(50L);
            Set<Integer> there = elsewhere.submit(() -> submit.armsFor(500L)).get();
            Set<Integer> here = Probe.taken();
            Probe.end();

            assertNotEquals(here, there);
            assertFalse(here.containsAll(there), "what the other thread took did not land here");
        } finally {
            elsewhere.shutdownNow();
        }
    }

    /** Nothing collecting means nothing recorded, rather than something recorded somewhere. */
    @Test
    void aRunNobodyIsMeasuringRecordsNothing() {
        Behavior submit = new Behavior(probed(compiled()));

        submit.apply(50L);   // outside begin()/end()

        assertEquals(Set.of(), Probe.taken());
    }

    // --- what the shipped classes do not mention -------------------------------------------------

    /**
     * A shipped class does not refer to the probe.
     *
     * <p>Not a matter of taste. {@code Probe} is the compiler's own class, and a jar that named it
     * would fail to resolve it anywhere the compiler is not on the path. Asked of the constant pool,
     * because that is the list a loader works through.
     */
    @Test
    void nothingThatShipsMentionsTheProbe() {
        Map<String, byte[]> shipped = compiled().db().ask(new Output.All()).value();
        assertNotNull(shipped);
        assertFalse(shipped.isEmpty());

        for (Map.Entry<String, byte[]> each : shipped.entrySet()) {
            assertFalse(referencedClasses(each.getValue()).contains(PROBE),
                    each.getKey() + " refers to the probe");
        }
    }

    /** And that check is not vacuous: the measured classes do name it. */
    @Test
    void theMeasuredClassesDoMentionIt() {
        Map<String, byte[]> classes = probed(compiled());

        assertTrue(classes.values().stream()
                        .anyMatch(bytes -> referencedClasses(bytes).contains(PROBE)),
                "something in there records where a run went");
    }

    /**
     * Measuring does not change what the program answers.
     *
     * <p>A measurement whose subject behaves differently under it is measuring something else. The
     * probe takes an {@code int} and returns nothing, so this ought to hold by construction — which is
     * a reason to check it rather than a reason not to.
     */
    @Test
    void aProbedClassAnswersWhatThePlainOneDoes() {
        Compilation compilation = compiled();
        Behavior measured = new Behavior(probed(compilation));
        Behavior plain = new Behavior(compilation.db()
                .ask(new Output.Linked(compilation.modules().get(0))).value());

        for (long cost : new long[] {-1L, 0L, 50L, 100L, 101L, 500L}) {
            assertEquals(String.valueOf(plain.apply(cost)), String.valueOf(measured.apply(cost)),
                    "at cost " + cost);
        }
    }

    /**
     * What a probed evaluation loads: this module measured, everything else as it is.
     *
     * <p>An import's arms belong to its own module and are numbered against its own plan. Measuring
     * them here would put hits into a run whose report has no plan to read them by, so the linked set
     * replaces this module's classes and leaves the rest alone.
     */
    @Test
    void onlyThisModulesClassesAreTheMeasuredOnes() {
        Compilation compilation = compiled();
        String module = compilation.modules().get(0);
        Map<String, byte[]> plain = compilation.db().ask(new Output.Linked(module)).value();
        Map<String, byte[]> measured = compilation.db()
                .ask(new Output.Evaluated(module, Output.CoverageMode.ARMS)).value();
        Map<String, byte[]> linked = compilation.db()
                .ask(new Output.EvaluationLinked(module, Output.CoverageMode.ARMS)).value();
        assertNotNull(plain);
        assertNotNull(linked);

        assertEquals(plain.keySet(), linked.keySet(), "the same classes are loadable");
        for (Map.Entry<String, byte[]> each : linked.entrySet()) {
            byte[] want = measured.containsKey(each.getKey())
                    ? measured.get(each.getKey()) : plain.get(each.getKey());
            assertEquals(referencedClasses(want), referencedClasses(each.getValue()),
                    each.getKey());
        }
        assertTrue(measured.keySet().stream().anyMatch(name ->
                        referencedClasses(linked.get(name)).contains(PROBE)),
                "this module's own classes are the measured ones");
    }

    // --- driving the generated classes -----------------------------------------------------------

    /** One set of generated classes, loaded and applied. */
    private static final class Behavior {

        private final Object instance;
        private final Method apply;

        Behavior(Map<String, byte[]> classes) {
            assertNotNull(classes, "the model under test compiles");
            ClassLoader loader = new MemoryClassLoader(classes,
                    ProbedBytecodeTest.class.getClassLoader());
            try {
                // The public name is an interface; the constructor and the erased apply are on $Impl.
                Class<?> impl = loader.loadClass("example.trip.Submit$Impl");
                Constructor<?> ctor = impl.getDeclaredConstructor();
                ctor.setAccessible(true);
                this.instance = ctor.newInstance();
                this.apply = impl.getDeclaredMethod("apply", Object.class);
                this.apply.setAccessible(true);
            } catch (ReflectiveOperationException e) {
                throw new AssertionError(e);
            }
        }

        Object apply(long cost) {
            try {
                return apply.invoke(instance, cost);
            } catch (ReflectiveOperationException e) {
                throw new AssertionError(e);
            }
        }

        Set<Integer> armsFor(long cost) {
            Probe.begin();
            try {
                apply(cost);
                return Probe.taken();
            } finally {
                Probe.end();
            }
        }
    }
}
