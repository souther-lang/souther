package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.execute.RunStop;
import souther.compiler.execute.StepsGotPast;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.runtime.ConstraintViolation;

import java.nio.charset.StandardCharsets;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * A run through classes generated to say where runs stop says the step it stopped at in the module
 * whose text the step is written in, whichever module's class ran it, and no step around it says
 * so in its stead; and code that ships says nothing of it.
 *
 * <p>The contract every reader of where a run stopped rests on, held here apart from any reader. A
 * helper of another module is inlined into the class of the behavior calling it, and its step is
 * still written in the helper's module; a behavior of another module is run as itself, and the
 * call to it is what the run was inside. In both the step stands inside an operation of the
 * caller's, which a run that stopped inside never got to.
 */
class AStepThatEndsARunSaysWhereItIsWrittenInTheModuleItIsWrittenInTest {

    private static final String LIB = """
            module lib

            let inc (n: Int): Int = n + 1

            behavior half : (n: Int) -> Int
            let half (n) = Rational.toInt(DOWN, 1 / n)
            """;

    private static final String APP = """
            module app

            import lib (inc, half)

            data In = { n: Int }
            data Out = Int

            behavior viaAHelper : (i: In) -> Out
            let viaAHelper (i) = Out { value = inc(i.n) * 2 }

            behavior viaABehavior : (i: In) -> Out
            let viaABehavior (i) = Out { value = half(i.n) + 1 }
            """;

    /** Both modules, compiled once for every case. */
    private static final class Model {

        static final Compilation COMPILED = ACompiledModel.compiles(
                Compilation.ofSources(List.of(LIB, APP), ModulePath.EMPTY));
        static final ClassLoader SAYING = COMPILED.loaderSayingWhereRunsStop("app")
                .orElseThrow(() -> new AssertionError("app is generated to say where runs stop"));
    }

    /** An operation is where its operator is written, and a call where what it calls is named. */
    private static final RunStop.Site SUM_IN_LIB = siteOf(LIB, "n + 1", "+");
    private static final RunStop.Site QUOTIENT_IN_LIB = siteOf(LIB, "1 / n", "/");
    private static final RunStop.Site PRODUCT_IN_APP = siteOf(APP, "inc(i.n) * 2", "*");
    private static final RunStop.Site CALL_IN_APP = siteOf(APP, "half(i.n)", "half");

    @Test
    void anOperationOfAHelperInlinedFromAnotherModuleIsWhereItIsWrittenThere() throws Exception {
        Ended ended = run("viaAHelper", Long.MAX_VALUE);

        assertEquals(Optional.of(SUM_IN_LIB), ended.site());
        assertEquals(List.of(), ended.inside(), "an inlined helper is no call");
        assertFalse(ended.gotPast().contains(PRODUCT_IN_APP),
                "the product around the sum is never got to: " + ended.gotPast());
    }

    @Test
    void anOperationOfABehaviorOfAnotherModuleIsWhereItIsWrittenThereInsideTheCall()
            throws Exception {
        Ended ended = run("viaABehavior", 0);

        assertEquals(Optional.of(QUOTIENT_IN_LIB), ended.site());
        assertEquals(List.of(Optional.of(CALL_IN_APP)), ended.inside());
    }

    /** A run that stops at nothing got past each step it worked out, in either module. */
    @Test
    void aRunThatStopsAtNothingGotPastEveryStepItWorkedOut() throws Exception {
        Object applied = Emitted.behavior(Model.SAYING, "app", "viaAHelper").getConstructor()
                .newInstance();
        Object in = Codecs.decoded(Model.SAYING, "app.In", Map.of("n", 1L));
        StepsGotPast.begin();
        try {
            Codecs.apply(applied, in);
        } finally {
            StepsGotPast.Account account = StepsGotPast.end();
            assertEquals(Set.of(SUM_IN_LIB, PRODUCT_IN_APP), account.gotPast());
            assertEquals(List.of(), account.inside(), "every call entered was left");
        }
    }

    /** What ships is generated without a word of it: no class refers to what records a run. */
    @Test
    void codeThatShipsSaysNothingOfWhereARunStops() {
        Map<String, ClassFileImage> shipped = Model.COMPILED.classes();
        assertFalse(shipped.isEmpty(), "the modules are generated");
        for (Map.Entry<String, ClassFileImage> each : shipped.entrySet()) {
            String held = new String(each.getValue().bytes(), StandardCharsets.ISO_8859_1);
            assertTrue(!held.contains("StepsGotPast") && !held.contains("placedAt"),
                    each.getKey() + " refers to what records where a run stops");
        }
    }

    /** Where a run stopped, the calls it was inside, and the steps it got past. */
    private record Ended(Optional<RunStop.Site> site, List<Optional<RunStop.Site>> inside,
                         Set<RunStop.Site> gotPast) {}

    /** Where {@code anchor}, the first of it inside the first {@code written}, is written in the
     *  module {@code source} declares: its line and its column, from one. */
    private static RunStop.Site siteOf(String source, String written, String anchor) {
        int at = source.indexOf(written) + written.indexOf(anchor);
        String module = source.substring("module ".length(), source.indexOf('\n'));
        String before = source.substring(0, at);
        return new RunStop.Site(module, (int) before.chars().filter(c -> c == '\n').count() + 1,
                at - before.lastIndexOf('\n'));
    }

    /** The run of app's {@code behavior} at {@code n}, which is to stop. */
    private static Ended run(String behavior, long n) throws Exception {
        Object applied = Emitted.behavior(Model.SAYING, "app", behavior).getConstructor()
                .newInstance();
        Object in = Codecs.decoded(Model.SAYING, "app.In", Map.of("n", n));
        StepsGotPast.begin();
        try {
            Codecs.apply(applied, in);
        } catch (ConstraintViolation stopped) {
            StepsGotPast.Account account = StepsGotPast.end();
            RunStop end = RunStop.ofTheEndOf(stopped).orElseThrow();
            if (!(end instanceof RunStop.AtAnEnd ended)) {
                return fail("the run stops at an operation: " + end);
            }
            return new Ended(ended.site(), account.inside(), account.gotPast());
        }
        StepsGotPast.end();
        return fail("the run of " + behavior + " at " + n + " stops");
    }
}
