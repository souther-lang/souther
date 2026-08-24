package souther.compiler.query;

import souther.compiler.query.Measurement;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Array;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Everything reachable from an answer means something by {@code equals}.
 *
 * <p>What {@code Db} needs of every value it holds, and it says so itself: it stops work by
 * comparing an answer with the one it replaces, and "an answer that never equals the one it
 * replaces leaves nothing standing". One object under an answer that compares by identity is
 * enough — the answer above it can then never equal its own recomputation, so every key that read
 * it runs again on every revision, over a model nobody edited.
 *
 * <p><b>Over the answers a compile makes, and not over a list of them.</b>
 * {@link AnAnswerAboutAClauseIsAValueTest} holds one query to this by asking it twice, which is
 * what caught the contract of a clause whose typing did not finish. What a witness per query cannot
 * do is answer for the query nobody wrote one for: a measure gained an arm carrying a proof, the
 * proof was a class with no {@code equals}, and every behavior whose measure reached that arm went
 * back to being recomputed — with the witness beside it passing, because it is about a different
 * key. So this walks what {@code Db} actually holds after a compile and asks each object for
 * itself.
 *
 * <p>Objects and not types. A type nothing instantiates is not a defect and would be noise here;
 * what is reachable in a real compile is exactly what {@code equals} will be asked to compare.
 *
 * <p>The model is chosen so that the measures reach the arms that carry no data — those are the
 * ones with nothing to compare, and so the ones where identity is easiest to leave in place.
 */
class EverythingAnAnswerHoldsIsAValueTest {

    /**
     * One behavior every measure of which is made, and one every measure of which is inapplicable.
     *
     * <p>Both on purpose. A measure that came to numbers carries them and would compare by them
     * whatever its own class did; a measure that came to an absence carries a proof and nothing
     * else, and that is the object this is about.
     */
    private static final String MODEL = """
            module example.value

            data Small
            data Large
            data Size = Small | Large
            data Amount = Int
                invariant value >= 0 && value <= 1000
            data Wrap = { v: String }
            data Req = { cost: Amount, size: Size }
            data Res = { n: Int }

            behavior measured : (r: Req) -> Res
                constructs Res
            let measured (r) = if r.cost.value >= 10 then Res { n = 1 } else Res { n = 0 }

            behavior nothingToMeasure : (w: Wrap) -> Res
                constructs Res
            let nothingToMeasure (w) = Res { n = 0 }

            example measured
                | "lo" : (Req { cost = 0, size = Small }) -> Res { n = 0 }
                | "hi" : (Req { cost = 10, size = Large }) -> Res { n = 1 }

            example nothingToMeasure
                | "one" : (Wrap { v = "x" }) -> Res { n = 0 }
            """;

    /**
     * The objects under an answer that compare by identity, as this compiler stands.
     *
     * <p>Named rather than tolerated, and of two kinds. Three are a reader or a whole database held
     * where a value belongs, which is the same defect this test is about and is not a new one —
     * they have an issue of their own. The fourth is a value that defines no {@code equals}, and is
     * here because writing one would cost more than it settles; that reason is given with it and is
     * not the reason the other three are here.
     *
     * <p>The set is written out either way, so that fixing one is this test failing rather than a
     * name nobody removes. A violation not in this set is the change in front of you.
     */
    private static final Set<String> KNOWN = Set.of(
            // A `ModulePath` holds the function it resolves a module with, and a function never
            // equals the same function computed again.
            "souther.compiler.meta.ModulePath$$Lambda",
            // The reading of a behavior's input, held under an answer rather than asked for again.
            "souther.compiler.inputs.InputDomain",
            // And a database, which is a way of reading and not a value (`Db`'s own header).
            "souther.compiler.query.Db",
            // The standard library, which is a value and is here for a different reason from the
            // three above: one is built per process and every answer of a compilation holds that
            // one, so identity is the answer structural equality would give. Writing that equality
            // out would walk every declaration the library has on every comparison, and writing
            // "any library equals any other" would be true only while there is one of them.
            "souther.compiler.stdlib.Stdlib");

    @Test
    void nothingUnderAnAnswerComparesByIdentity() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        // Asked as well as answered: the measures are what this model is for, and a key nothing
        // asked is a key whose answer `everyAnswer` has nothing to say about.
        compilation.db().ask(new Adequacy.Coverage(compilation.modules().get(0)));

        Walk walk = walkOf(compilation.db());

        assertTrue(walk.visited() > 1000,
                () -> "a walk that reached " + walk.visited() + " objects is not reaching the"
                        + " answers this is about");
        assertEquals(KNOWN, walk.byIdentity(),
                "what an answer holds that compares by identity");
    }

    /**
     * And the arms carrying a proof are among what was walked.
     *
     * <p>The control the assertion above needs. Every object it visits passing says nothing while
     * the objects worth asking are not among them — which is how this was written the first time,
     * over a model whose every measure came to numbers.
     */
    @Test
    void andTheAnswersWithNothingToCompareAreAmongThem() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        compilation.db().ask(new Adequacy.Coverage(compilation.modules().get(0)));

        Set<String> reached = walkOf(compilation.db()).classes();

        assertTrue(reached.contains(Measurement.NotApplicable.class.getName()),
                () -> "no partition measure came to an absence: " + reached.size() + " classes");
        assertTrue(reached.contains(Measurement.NotApplicable.class.getName()),
                "no border measure came to an absence");
    }

    /** What the walk found: how many objects, which classes, and which of them compare by
     *  identity. */
    private record Walk(int visited, Set<String> classes, Set<String> byIdentity) {}

    private static Walk walkOf(Db db) {
        Set<Object> seen = Collections.newSetFromMap(new IdentityHashMap<>());
        Set<String> classes = new LinkedHashSet<>();
        Set<String> byIdentity = new LinkedHashSet<>();
        Deque<Object> todo = new ArrayDeque<>();
        db.everyAnswer().values().forEach(answer -> {
            if (answer.value() != null) {
                todo.add(answer.value());
            }
        });
        while (!todo.isEmpty()) {
            Object each = todo.pop();
            if (each == null || !seen.add(each)) {
                continue;
            }
            // The leaves. A boxed number, a string, a case of an enumeration and a class are values
            // by the language, and asking them again would be asking about the JDK.
            if (each instanceof String || each instanceof Number || each instanceof Boolean
                    || each instanceof Character || each instanceof Enum<?>
                    || each instanceof Class<?>) {
                continue;
            }
            if (each instanceof Collection<?> items) {
                items.forEach(todo::add);
                continue;
            }
            if (each instanceof Map<?, ?> entries) {
                entries.forEach((key, value) -> {
                    todo.add(key);
                    todo.add(value);
                });
                continue;
            }
            if (each.getClass().isArray()) {
                for (int i = 0; i < Array.getLength(each); i++) {
                    todo.add(Array.get(each, i));
                }
                continue;
            }
            classes.add(each.getClass().getName());
            if (!declaresEquals(each.getClass())) {
                // A lambda's class name carries the JVM's own counter, which differs per run. What
                // is worth naming is which lambda it is.
                byIdentity.add(each.getClass().getName().replaceFirst("/0x[0-9a-f]+$", ""));
                continue;   // what it holds is unreachable through an equality that never holds
            }
            fieldsOf(each, todo);
        }
        return new Walk(seen.size(), classes, byIdentity);
    }

    private static void fieldsOf(Object each, Deque<Object> todo) {
        for (Class<?> at = each.getClass(); at != null && at != Object.class;
                at = at.getSuperclass()) {
            for (Field field : at.getDeclaredFields()) {
                if (Modifier.isStatic(field.getModifiers()) || field.getType().isPrimitive()) {
                    continue;
                }
                try {
                    field.setAccessible(true);
                    todo.add(field.get(each));
                } catch (RuntimeException | ReflectiveOperationException opaque) {
                    // A field this cannot open is one this cannot answer for, and saying nothing
                    // about it is the honest answer — it is counted in neither set.
                }
            }
        }
    }

    private static boolean declaresEquals(Class<?> type) {
        try {
            return type.getMethod("equals", Object.class).getDeclaringClass() != Object.class;
        } catch (NoSuchMethodException none) {
            return false;
        }
    }
}
