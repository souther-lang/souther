package souther.compiler;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A rule may quantify over a collection, and the fold that becomes is the module's to emit.
 *
 * <p>{@code List.all} and the rest of the quantifiers are ordinary library helpers derived from the
 * fold, so a rule naming one holds a call to the library's one recursion once it has been expanded —
 * and a recursion cannot be expanded away, so the module holding that rule emits a method for it.
 * That is true of a rule for exactly the reason it is true of a body, and a module reaching a
 * quantifier from a rule and from nowhere else was not being given the method: what it had to emit
 * was worked out by listing the places a module writes expressions, and a rule was not one of them.
 *
 * <p>Held end to end, because the middle is where it went wrong in three different ways as the
 * answer moved: no signature to type the call against, then no method to call, then no elaborated
 * body to emit the method from. What settles it is that the program runs.
 */
class ARuleReachingAQuantifierGetsTheFoldItBecomesTest {

    private static final String ONLY_FROM_A_RULE = """
            module quantified

            data Age = Int
                invariant value >= 0

            data Person = { age: Age }

            data Count = Int
                invariant value >= 0

            behavior countAdults : (people: List<Person>) -> Count
                ensures grown = List.all(p -> p.age.value >= 18, people) && value.value >= 0
            """;

    /** Every emitted class, loaded — which is where the JVM verifies each method it holds. */
    private static Class<?> loadingAll(Map<String, byte[]> classes, String named) {
        BytesClassLoader loader = new BytesClassLoader(classes,
                ARuleReachingAQuantifierGetsTheFoldItBecomesTest.class.getClassLoader());
        for (String name : classes.keySet()) {
            assertDoesNotThrow(() -> Class.forName(name, true, loader), name);
        }
        return assertDoesNotThrow(() -> Class.forName(named, true, loader));
    }

    @Test
    void aModuleWhoseOnlyQuantifierIsInARuleCompiles() {
        assertDoesNotThrow(() -> Compiler.compile(ONLY_FROM_A_RULE));
    }

    /** And emits the fold, which is the method the expanded rule holds a call to. */
    @Test
    void andEmitsTheFoldTheRuleExpandedTo() throws Exception {
        Map<String, byte[]> classes = Compiler.compile(ONLY_FROM_A_RULE);
        Class<?> fns = loadingAll(classes, "quantified.$Fns");

        Method fold = fns.getDeclaredMethod("List$foldFrom",
                Object.class, Object.class, Object.class, Object.class);
        assertNotNull(fold);
        fold.setAccessible(true);

        souther.runtime.Fn step = args -> (Boolean) args[0] && (Long) args[1] >= 18L;
        assertEquals(Boolean.TRUE, fold.invoke(null, step, Boolean.TRUE, List.of(20L, 30L), 0L));
        assertEquals(Boolean.FALSE, fold.invoke(null, step, Boolean.TRUE, List.of(20L, 7L), 0L));
    }

    /**
     * A recursion another module published, reached from a rule and from nowhere else. The same
     * mistake, and it did not even reach a report: the call was typed against nothing and the check
     * failed inside this compiler.
     */
    @Test
    void andSoDoesARuleReachingARecursionAnotherModulePublished() {
        String lib = """
                module chart exposing ( Emp, depth )

                data Emp = { boss: Emp? }

                let depth (e: Emp) : Int =
                    match e.boss with
                        | Some b -> 1 + depth(b)
                        | None   -> 0
                """;
        String user = """
                module reports

                import chart as Chart ( Emp, depth )

                data Rank = Int

                behavior rankOf : (e: Emp) -> Rank
                    ensures deep = value.value >= depth(e)
                """;

        assertDoesNotThrow(() -> Compiler.compileModules(List.of(lib, user)));
    }

    /**
     * And where something else in the module reaches the same quantifier, which is how the mistake
     * stayed hidden: the fold arrived for the other reader's sake and the rule was carried by it.
     */
    @Test
    void andWhereADefinitionReachesTheSameQuantifierToo() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module both

                data Count = Int
                    invariant value >= 0

                behavior countIt : (xs: List<Int>) -> Count
                    ensures nonNegative = List.all(x -> x >= 0, xs) && value.value >= 0

                let anyNegative (ys: List<Int>) : Bool = List.any(y -> y < 0, ys)
                """));
    }
}
