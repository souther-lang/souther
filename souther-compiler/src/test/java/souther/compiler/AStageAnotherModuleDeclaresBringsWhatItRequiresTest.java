package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A composition requires what its stages require (spec §composition-with-requirements), and a stage
 * another module declares is no exception: what it requires is what its module worked out, whether
 * that module is compiled here or read off the path. The composition takes those dependencies
 * injected and hands them to the stage when it builds it, so both the composition's constructor and
 * the stage's constructor are read here, by running them.
 *
 * <p>Whether a class holds a behavior in a field or builds it is decided by whether Java supplies
 * it, and by nothing else. The rows at the end are the ones where being some other behavior's
 * dependency made a behavior with an implementation look like one Java supplies.
 */
class AStageAnotherModuleDeclaresBringsWhatItRequiresTest {

    /** A composition over an injected stage, and a behavior with a body that depends on it. */
    private static final String LIB = """
            module lib.q exposing ( rate, double, priced : Int, charged )
            behavior rate : (n: Int) -> Int
            behavior double : (n: Int) -> Int
            let double (n) = n + n
            behavior priced = rate >-> double
            behavior charged : (n: Int) -> Int depends on rate
            let charged (n, rate) = rate(n)
            """;

    /** Names neither `rate` nor anything that requires it by name. */
    private static final String APP = """
            module app.v
            import lib.q ( priced, double, charged )
            behavior again = priced >-> double
            behavior billed = charged >-> double
            """;

    private static final String RATE = """
            package lib.q;
            public final class RateImpl extends Rate {
                public Long apply(Long n) { return n * 10; }
            }
            """;

    /** Both modules compiled together, with a Java `rate`, once for every case that runs them: the
     *  classes are read and nothing a case does changes them. */
    private static final Map<String, ClassFileImage> TOGETHER = together();

    private static Map<String, ClassFileImage> together() {
        try {
            return Map.copyOf(withRate(Compiler.compileModules(List.of(LIB, APP))));
        } catch (Exception e) {
            throw new ExceptionInInitializerError(e);
        }
    }

    @Test
    void aCompositionOfAnotherModuleIsBuiltWithWhatItsStagesRequire() throws Exception {
        Object again = bound(TOGETHER, "app.v.Again", "lib.q.Rate");

        assertEquals(120L, Codecs.apply(again, 3L), "rate(3) is 30, doubled by priced and again");
    }

    @Test
    void aBehaviorOfAnotherModuleThatDependsOnSomethingIsBuiltWithIt() throws Exception {
        Object billed = bound(TOGETHER, "app.v.Billed", "lib.q.Rate");

        assertEquals(60L, Codecs.apply(billed, 3L));
    }

    /** The same two, with the declaring module read off the path. What its compositions require
     *  comes from what it published, since the stages behind them are not carried. */
    @Test
    void aModuleReadOffThePathAnswersTheSame() throws Exception {
        Map<String, ClassFileImage> lib = Compiler.compile(LIB);
        Map<String, ClassFileImage> classes = new HashMap<>(lib);
        classes.putAll(Compiler.compileModules(List.of(APP), ModulePath.of(lib)));
        Map<String, ClassFileImage> run = withRate(classes);

        assertEquals(120L, Codecs.apply(bound(run, "app.v.Again", "lib.q.Rate"), 3L));
        assertEquals(60L, Codecs.apply(bound(run, "app.v.Billed", "lib.q.Rate"), 3L));
    }

    /** Two dependencies from two modules, three modules deep, with the first two read off the path.
     *  The top composition takes them in the order the stages reach them. */
    @Test
    void whatIsRequiredCarriesThroughEveryModuleInOrder() throws Exception {
        Map<String, ClassFileImage> lower = Compiler.compileModules(List.of("""
                module lib.r exposing ( rate, double, step : Int )
                behavior rate : (n: Int) -> Int
                behavior double : (n: Int) -> Int
                let double (n) = n + n
                behavior step = rate >-> double
                """, """
                module lib.p exposing ( tax, priced : Int )
                import lib.r ( step )
                behavior tax : (n: Int) -> Int
                behavior priced = step >-> tax
                """));
        Map<String, ClassFileImage> classes = new HashMap<>(lower);
        classes.putAll(Compiler.compileModules(List.of("""
                module app.w
                import lib.p ( priced )
                behavior inc : (n: Int) -> Int
                let inc (n) = n + 1
                behavior again = priced >-> inc
                """), ModulePath.of(lower)));
        classes.put("lib.r.RateImpl", Subclasses.compile(classes, "lib.r.RateImpl", """
                package lib.r;
                public final class RateImpl extends Rate {
                    public Long apply(Long n) { return n * 10; }
                }
                """));
        classes.put("lib.p.TaxImpl", Subclasses.compile(classes, "lib.p.TaxImpl", """
                package lib.p;
                public final class TaxImpl extends Tax {
                    public Long apply(Long n) { return n + 1; }
                }
                """));

        Object again = bound(classes, "app.w.Again", "lib.r.Rate", "lib.p.Tax");

        assertEquals(62L, Codecs.apply(again, 3L), "rate, then double, then tax, then inc");
    }

    /** A dependency the module never names that takes two inputs: held as its own class and not
     *  as the unary Behavior, which is decided by its signature, so the signature has to reach
     *  here without an import bringing it. */
    @Test
    void aDependencyNobodyHereNamesIsHeldAsWhatItsSignatureSays() throws Exception {
        Map<String, ClassFileImage> classes = new HashMap<>(Compiler.compileModules(List.of("""
                module lib.m exposing ( double, priced : Int )
                behavior pair : (n: Int, m: Int) -> Int
                behavior double : (n: Int) -> Int
                let double (n) = n + n
                behavior priced = pair >-> double
                """, """
                module app.m
                import lib.m ( priced, double )
                behavior again = priced >-> double
                """)));
        classes.put("lib.m.PairImpl", Subclasses.compile(classes, "lib.m.PairImpl", """
                package lib.m;
                public final class PairImpl extends Pair {
                    public Long apply(Long n, Long m) { return n * 10 + m; }
                }
                """));

        Object again = bound(classes, "app.m.Again", "lib.m.Pair");

        assertEquals(136L, applied(again, 3L, 4L), "pair(3, 4) is 34, doubled twice");
    }

    /** A behavior one behavior depends on and a composition builds as a stage. The composition was
     *  handed what the stage requires, not the stage, so it builds it. */
    @Test
    void aStageAnotherBehaviorDependsOnIsStillBuilt() throws Exception {
        Map<String, ClassFileImage> classes = new HashMap<>(Compiler.compileModules(List.of("""
                module one.m
                behavior rate : (n: Int) -> Int
                behavior x : (n: Int) -> Int depends on rate
                let x (n, rate) = rate(n)
                behavior a : (n: Int) -> Int depends on x
                let a (n, x) = x(n)
                behavior double : (n: Int) -> Int
                let double (n) = n + n
                behavior c = x >-> double
                """)));
        classes.put("one.m.RateImpl", Subclasses.compile(classes, "one.m.RateImpl", """
                package one.m;
                public final class RateImpl extends Rate {
                    public Long apply(Long n) { return n * 10; }
                }
                """));

        Object c = bound(classes, "one.m.C", "one.m.Rate");

        assertEquals(60L, Codecs.apply(c, 3L));
    }

    /** The same with two inputs, where the stage is the first one and is applied on its own class:
     *  the one built here, and not a base Java extends. */
    @Test
    void aFirstStageAnotherBehaviorDependsOnIsAppliedOnWhatWasBuilt() throws Exception {
        Map<String, ClassFileImage> classes = new HashMap<>(Compiler.compileModules(List.of("""
                module three.m
                behavior rate : (n: Int) -> Int
                behavior x : (n: Int, m: Int) -> Int depends on rate
                let x (n, m, rate) = rate(n) + m
                behavior a : (n: Int) -> Int depends on x
                let a (n, x) = x(n, n)
                behavior double : (n: Int) -> Int
                let double (n) = n + n
                behavior c = x >-> double
                """)));
        classes.put("three.m.RateImpl", Subclasses.compile(classes, "three.m.RateImpl", """
                package three.m;
                public final class RateImpl extends Rate {
                    public Long apply(Long n) { return n * 10; }
                }
                """));

        Object c = bound(classes, "three.m.C", "three.m.Rate");

        assertEquals(68L, applied(c, 3L, 4L), "x(3, 4) is 34, doubled");
    }

    /** A dependency with a body of its own that takes two inputs is held as its interface, and a
     *  call on it is linked against the interface rather than a class Java extends. */
    @Test
    void aDependencyWithABodyIsCalledThroughItsInterface() throws Exception {
        Map<String, ClassFileImage> classes = new HashMap<>(Compiler.compileModules(List.of("""
                module two.m
                behavior rate : (n: Int) -> Int
                behavior x : (n: Int, m: Int) -> Int depends on rate
                let x (n, m, rate) = rate(n) + m
                behavior a : (n: Int) -> Int depends on x
                let a (n, x) = x(n, n)
                """)));
        classes.put("two.m.RateImpl", Subclasses.compile(classes, "two.m.RateImpl", """
                package two.m;
                public final class RateImpl extends Rate {
                    public Long apply(Long n) { return n * 10; }
                }
                """));
        BytesClassLoader loader = new BytesClassLoader(classes, getClass().getClassLoader());
        Object rate = loader.loadClass("two.m.RateImpl").getConstructor().newInstance();
        Object x = loader.loadClass("two.m.X").getMethod("bind", loader.loadClass("two.m.Rate"))
                .invoke(null, rate);
        Object a = loader.loadClass("two.m.A").getMethod("bind", loader.loadClass("two.m.X"))
                .invoke(null, x);

        assertEquals(33L, Codecs.apply(a, 3L));
    }

    /**
     * An example of the composition stands in for each dependency its foreign stage brings in, in
     * the order the constructor takes them. The row only answers 14 with `rate` applied first and
     * `bonus` to what it answered; with the two tables bound the other way round it answers 0.
     */
    private static final String TWO_DEPENDENCIES = """
            module lib.e exposing ( rate, bonus, double, priced : Int )
            behavior rate : (n: Int) -> Int
            behavior bonus : (n: Int) -> Int
            behavior double : (n: Int) -> Int
            let double (n) = n + n
            behavior priced = rate >-> bonus
            """;

    private static String exampled(int answer) {
        return """
                module app.e
                import lib.e ( priced, double )
                behavior again = priced >-> double

                fake lib.e.rate
                    | (1) -> 10
                    | _   -> 0

                fake lib.e.bonus
                    | (10) -> 7
                    | _    -> 0

                example again
                    | (1) -> %d
                """.formatted(answer);
    }

    @Test
    void anExampleHandsEachFakeToTheDependencyItStandsFor() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(TWO_DEPENDENCIES, exampled(14))));
        assertEquals("E1905", assertThrows(CompileException.class,
                        () -> Compiler.compileModules(List.of(TWO_DEPENDENCIES, exampled(0))))
                .diagnostic().code(), "the row is run, so a wrong answer is refused");
    }

    private static Map<String, ClassFileImage> withRate(Map<String, ClassFileImage> classes)
            throws Exception {
        Map<String, ClassFileImage> all = new HashMap<>(classes);
        all.put("lib.q.RateImpl", Subclasses.compile(classes, "lib.q.RateImpl", RATE));
        return all;
    }

    /** {@code behavior} built by its {@code bind}, handed one implementation of each base named, in
     *  that order — so a factory that takes them in another order, or other ones, does not link. */
    private static Object bound(Map<String, ClassFileImage> classes, String behavior,
                                String... bases) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(classes, AStageAnotherModuleDeclaresBringsWhatItRequiresTest.class.getClassLoader());
        Class<?>[] types = new Class<?>[bases.length];
        Object[] args = new Object[bases.length];
        for (int i = 0; i < bases.length; i++) {
            types[i] = loader.loadClass(bases[i]);
            args[i] = loader.loadClass(bases[i] + "Impl").getConstructor().newInstance();
        }
        return loader.loadClass(behavior).getMethod("bind", types).invoke(null, args);
    }

    /** Applies a behavior taking two inputs through its erased {@code apply}. */
    private static Object applied(Object behavior, Object first, Object second) throws Exception {
        Method apply = Arrays.stream(behavior.getClass().getMethods())
                .filter(m -> m.getName().equals("apply") && m.getParameterCount() == 2
                        && m.getParameterTypes()[0] == Object.class)
                .findFirst().orElseThrow();
        return apply.invoke(behavior, first, second);
    }
}
