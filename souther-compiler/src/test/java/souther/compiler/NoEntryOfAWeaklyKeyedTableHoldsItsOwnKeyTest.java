package souther.compiler;

import java.io.IOException;
import java.lang.ref.Reference;
import java.lang.reflect.Array;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.net.URISyntaxException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;
import java.util.WeakHashMap;
import java.util.stream.Stream;

import net.unit8.notation199x.pattern.Meter;

import org.junit.jupiter.api.Test;

import souther.compiler.meaning.CompoundSamples;
import souther.compiler.meaning.CountsWrittenOut;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WaysSamples;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.regex.Language;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * No value a table keyed weakly holds reaches the key it is held under.
 *
 * <p>A key held weakly is let go once nothing holds it strongly, and the table's own value is
 * something: a value that reaches its key keeps the key, and so the entry, for as long as the
 * table is there, which for a table held statically is as long as the compiler runs. Nothing in
 * the type says so — a value may reach its key through anything it holds — so it is asked of the
 * values themselves, by following every reference each holds strongly.
 *
 * <p>Every table keyed weakly that this compiler holds statically is found from what it is
 * compiled to, and each is filled through the way the compiler fills it before it is asked: a
 * table this does not know how to fill is one the second question would be asked of nothing.
 */
class NoEntryOfAWeaklyKeyedTableHoldsItsOwnKeyTest {

    private static final Meter ROOMY = new Meter(100_000, 10_000_000, 1_000_000_000L);

    /** What the tables are filled with, held here so that no entry is let go before it is read. */
    private static final List<Object> KEPT = new ArrayList<>();

    /** Each table, by the class and the field holding it, and how the compiler fills it. */
    private static final Map<String, Runnable> FILLED_BY = Map.of(
            "souther.compiler.coverage.DecisionSources$LibraryPart#KEPT", () -> {
                Compilation compilation = Compilation.ofSource("""
                        module example.weak

                        behavior pick : (n: Int) -> Int
                        let pick (n) = if Int.abs(n) > 3 then 1 else 0
                        """, "Main");
                compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.OFF));
                compilation.answerEverything();
                KEPT.add(compilation);
            },
            "souther.compiler.partition.OnTheWay$OneOf#MADE", () -> {
                Compilation compilation = Compilation.ofSource("""
                        module example.weak

                        behavior pick : (x: Int, j: Int) -> Bool
                        let pick (x, j) = {
                            let a0 = x >= 0
                            let a1 = a0 && (j > 3 || a0)
                            a1 && (j > 3 || a1)
                        }
                        """, "Main");
                compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.ALL));
                ACompiledModel.compiles(compilation);
                AdequacyReport.of(compilation);
                KEPT.add(compilation);
            },
            "souther.compiler.regex.EndsOfAMachine#HELD", () -> {
                Language words = Language.ofWords(List.of("ab", "cde"), ROOMY);
                words.lengths();
                words.sumsOfCodePoints();
                words.codePointsAt(0);
                KEPT.add(words);
            },
            "souther.compiler.regex.StringsHeldAsWritten#MADE", () -> {
                Language words = Language.ofWords(List.of("fg", "hij"), ROOMY);
                words.heldAsWritten();
                KEPT.add(words);
            },
            "souther.compiler.meaning.SharedPropositions#KEPT", () ->
                    KEPT.add(CompoundSamples.numberAtLeastZero("n").denied()),
            "souther.compiler.meaning.SharedPropositions#CHOICES", () -> {
                Proposition counted = count();
                CountsWrittenOut.of(counted);
                KEPT.add(counted);
            },
            "souther.compiler.meaning.SharedPropositions#WRITTEN", () -> {
                Proposition.OfTheWays ways = WaysSamples.over(CompoundSamples.truth("w"));
                ways.written();
                KEPT.add(ways);
            },
            "souther.compiler.meaning.CountsWrittenOut#HANDED", () -> {
                Proposition counted = count();
                CountsWrittenOut.of(counted);
                KEPT.add(counted);
            },
            "souther.compiler.meaning.CountsWrittenOut#HANDED_OUTSIDE_ELEMENTS", () -> {
                Proposition counted = count();
                CountsWrittenOut.outsideElementsOf(counted);
                KEPT.add(counted);
            });

    private static Proposition count() {
        return CompoundSamples.holding(Proposition.SoManyHold.class, CompoundSamples.truth("a"),
                CompoundSamples.truth("b"), null);
    }

    @Test
    void everyTableKeyedWeaklyIsOneThisKnowsHowToFill() throws Exception {
        assertEquals(new TreeSet<>(FILLED_BY.keySet()), new TreeSet<>(tablesKeyedWeakly()));
    }

    @Test
    void noValueReachesTheKeyItIsHeldUnder() throws Exception {
        for (Map.Entry<String, Runnable> table : FILLED_BY.entrySet()) {
            table.getValue().run();
            List<Map.Entry<?, ?>> entries = entriesOf(table.getKey());
            assertFalse(entries.isEmpty(), () -> table.getKey() + " is filled before it is asked");
            for (Map.Entry<?, ?> entry : entries) {
                if (entry.getKey() == null) {
                    continue;
                }
                List<String> way = wayFrom(entry.getValue(), entry.getKey());
                assertTrue(way == null, () -> table.getKey() + " holds a value that reaches its"
                        + " key, which is never let go: " + String.join(" -> ", way));
            }
        }
    }

    /** Each static field of this compiler's that holds a table keyed weakly, as class#field. */
    private static Set<String> tablesKeyedWeakly() throws IOException, URISyntaxException,
            ReflectiveOperationException {
        Path classes = Path.of(Language.class.getProtectionDomain().getCodeSource().getLocation()
                .toURI());
        byte[] named = "java/util/WeakHashMap".getBytes(StandardCharsets.US_ASCII);
        List<String> mentioning = new ArrayList<>();
        try (Stream<Path> files = Files.walk(classes)) {
            for (Path file : files.filter(each -> each.toString().endsWith(".class")).toList()) {
                if (contains(Files.readAllBytes(file), named)) {
                    String relative = classes.relativize(file).toString();
                    mentioning.add(relative.substring(0, relative.length() - ".class".length())
                            .replace(file.getFileSystem().getSeparator(), "."));
                }
            }
        }
        Set<String> tables = new TreeSet<>();
        for (String name : mentioning) {
            for (Field field : Class.forName(name).getDeclaredFields()) {
                if (!Modifier.isStatic(field.getModifiers())
                        || !Map.class.isAssignableFrom(field.getType())) {
                    continue;
                }
                field.setAccessible(true);
                Object held = field.get(null);
                if (held instanceof WeakHashMap<?, ?> || (held != null && held.getClass().getName()
                        .equals("java.util.Collections$SynchronizedMap"))) {
                    tables.add(name + "#" + field.getName());
                }
            }
        }
        return tables;
    }

    private static boolean contains(byte[] bytes, byte[] part) {
        outer:
        for (int at = 0; at + part.length <= bytes.length; at++) {
            for (int i = 0; i < part.length; i++) {
                if (bytes[at + i] != part[i]) {
                    continue outer;
                }
            }
            return true;
        }
        return false;
    }

    private static List<Map.Entry<?, ?>> entriesOf(String table)
            throws ReflectiveOperationException {
        String[] at = table.split("#");
        Field field = Class.forName(at[0]).getDeclaredField(at[1]);
        field.setAccessible(true);
        Map<?, ?> map = (Map<?, ?>) field.get(null);
        synchronized (map) {
            return new ArrayList<>(map.entrySet());
        }
    }

    /**
     * The fields leading from {@code from} to {@code target} through references held strongly, or
     * null where none does.
     *
     * <p>A reference object is held weakly or softly and leads nowhere. A collection, a map or an
     * {@link Optional} of the JDK's leads to what it holds, read through what it answers; any
     * other class of the JDK's is taken to hold nothing of this compiler's.
     */
    private static List<String> wayFrom(Object from, Object target)
            throws IllegalAccessException {
        Map<Object, List<String>> seen = new IdentityHashMap<>();
        Deque<Object> next = new ArrayDeque<>();
        seen.put(from, List.of("value"));
        next.add(from);
        while (!next.isEmpty()) {
            Object at = next.poll();
            if (at == target) {
                return seen.get(at);
            }
            for (Map.Entry<String, Object> held : heldBy(at)) {
                if (held.getValue() != null && !seen.containsKey(held.getValue())) {
                    List<String> way = new ArrayList<>(seen.get(at));
                    way.add(held.getKey());
                    seen.put(held.getValue(), way);
                    next.add(held.getValue());
                }
            }
        }
        return null;
    }

    private static List<Map.Entry<String, Object>> heldBy(Object at)
            throws IllegalAccessException {
        List<Map.Entry<String, Object>> held = new ArrayList<>();
        if (at instanceof Reference<?>) {
            return held;
        }
        if (at.getClass().isArray()) {
            if (!at.getClass().getComponentType().isPrimitive()) {
                for (int i = 0; i < Array.getLength(at); i++) {
                    add(held, "[" + i + "]", Array.get(at, i));
                }
            }
            return held;
        }
        if (at instanceof Map<?, ?> map) {
            for (Map.Entry<?, ?> each : List.copyOf(map.entrySet())) {
                add(held, "key", each.getKey());
                add(held, "value of " + each.getKey(), each.getValue());
            }
            return held;
        }
        if (at instanceof Collection<?> all) {
            int i = 0;
            for (Object each : List.copyOf(all)) {
                add(held, "element " + i++, each);
            }
            return held;
        }
        if (at instanceof Optional<?> maybe) {
            maybe.ifPresent(inside -> add(held, "inside", inside));
            return held;
        }
        for (Class<?> type = at.getClass(); type != null && !type.getName().startsWith("java.");
             type = type.getSuperclass()) {
            for (Field field : type.getDeclaredFields()) {
                if (Modifier.isStatic(field.getModifiers()) || field.getType().isPrimitive()) {
                    continue;
                }
                field.setAccessible(true);
                add(held, type.getSimpleName() + "." + field.getName(), field.get(at));
            }
        }
        return held;
    }

    private static void add(List<Map.Entry<String, Object>> held, String how, Object what) {
        if (what != null) {
            held.add(Map.entry(how, what));
        }
    }
}
