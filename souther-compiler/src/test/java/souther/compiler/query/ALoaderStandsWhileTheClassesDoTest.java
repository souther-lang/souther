package souther.compiler.query;

import souther.compiler.jvm.ClassFileImage;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * The rule a loader is kept by, asked of it directly.
 *
 * <p>{@code ACompilationAnswersWithOneLoaderForItsClassesTest} drives it through edits, which is
 * what a caller does and is what says the rule is wired to a real compile. What an edit cannot
 * reliably produce is the case the rule exists for: two class sets that are not the same map and
 * are the same class files. That is a generation that ran again and came to what it came to before
 * — the whole of what holding classes as values buys — and a loader replaced over it divides every
 * type of a program nothing about has changed.
 *
 * <p>So the two maps are made here. A rule that can only be reached through a scenario is a rule
 * whose branches are covered by whatever the scenario happens to reach, and this one is not.
 */
class ALoaderStandsWhileTheClassesDoTest {

    private static Map<String, ClassFileImage> classes(String said) {
        Map<String, ClassFileImage> out = new LinkedHashMap<>();
        out.put("demo.Thing", ClassFileImage.of(said.getBytes(java.nio.charset.StandardCharsets.UTF_8)));
        return out;
    }

    /** A loader nobody looks into: what is asked here is which one comes back, never what it loads. */
    private static ClassLoader aLoader() {
        return new ClassLoader(null) { };
    }

    @Test
    void twoMapsOfOneProgramAreOneLoader() {
        Map<String, ClassFileImage> first = classes("a");
        Map<String, ClassFileImage> second = classes("a");
        assertNotSame(first, second, "two maps");
        assertEquals(first, second, "of one program");

        LoaderOverClasses kept = new LoaderOverClasses();
        ClassLoader over = kept.of(first, ALoaderStandsWhileTheClassesDoTest::aLoader);

        assertSame(over, kept.of(second, ALoaderStandsWhileTheClassesDoTest::aLoader),
                "a program that was built again is the program that was loaded");
    }

    /** And the map it was handed the first time is not what it holds them to. */
    @Test
    void andTheSameMapIsToo() {
        Map<String, ClassFileImage> only = classes("a");
        LoaderOverClasses kept = new LoaderOverClasses();
        ClassLoader over = kept.of(only, ALoaderStandsWhileTheClassesDoTest::aLoader);

        assertSame(over, kept.of(only, ALoaderStandsWhileTheClassesDoTest::aLoader));
    }

    @Test
    void twoProgramsAreTwoLoaders() {
        LoaderOverClasses kept = new LoaderOverClasses();
        ClassLoader over = kept.of(classes("a"), ALoaderStandsWhileTheClassesDoTest::aLoader);

        assertNotSame(over, kept.of(classes("b"), ALoaderStandsWhileTheClassesDoTest::aLoader),
                "a program that came out different is a different program");
    }

    /** Nothing is built while the classes stand, which is what "kept" means and not only which
     *  object comes back. */
    @Test
    void nothingIsBuiltWhileTheClassesStand() {
        AtomicInteger built = new AtomicInteger();
        LoaderOverClasses kept = new LoaderOverClasses();
        kept.of(classes("a"), () -> {
            built.incrementAndGet();
            return aLoader();
        });
        kept.of(classes("a"), () -> {
            built.incrementAndGet();
            return aLoader();
        });

        assertEquals(1, built.get());
    }

    /**
     * A loader that could not be built claims nothing.
     *
     * <p>The classes are recorded once there is a loader over them and not before, so an ask that
     * raised is an ask that changed nothing — and the next one is not answered with the loader from
     * before the edit, which would be a loader over a program its caller is no longer compiling.
     */
    @Test
    void oneThatCouldNotBeBuiltClaimsNothing() {
        LoaderOverClasses kept = new LoaderOverClasses();
        ClassLoader first = kept.of(classes("a"), ALoaderStandsWhileTheClassesDoTest::aLoader);

        assertThrows(IllegalStateException.class, () -> kept.of(classes("b"), () -> {
            throw new IllegalStateException("this path cannot be read just now");
        }));

        assertNotSame(first, kept.of(classes("b"), ALoaderStandsWhileTheClassesDoTest::aLoader),
                "the ask after it is over the classes there are");
    }
}
