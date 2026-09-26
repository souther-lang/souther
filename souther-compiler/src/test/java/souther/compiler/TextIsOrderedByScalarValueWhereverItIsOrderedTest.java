package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.Text;
import souther.compiler.regex.Language;
import souther.compiler.regex.PatternPlan;
import souther.runtime.Representations;
import souther.runtime.Strings;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Text is ordered one way wherever it is ordered: lexicographically over Unicode scalar values
 * (spec §equality), which is what {@link Strings#compare} answers.
 *
 * <p>Held as one law over the places that order text rather than as a test of each: a model's
 * {@code <}, the sort family, a newtype over text, the order a boundary writes a set's members and a
 * map's keys in, where the compiler draws a line between two strings and what it reads a rule over
 * text to leave. Every one of them is asked about the same pairs and has to answer what
 * {@link Strings#compare} answers. A place that reached for {@link String#compareTo} instead would
 * pass every pair of letters, so the pairs are the ones where the two part: a character past the
 * basic plane against one in {@code U+E000..U+FFFF}, where the first unit of the pair is below the
 * other character's only unit.
 */
class TextIsOrderedByScalarValueWhereverItIsOrderedTest {

    private static String text(int... codePoints) {
        return new String(codePoints, 0, codePoints.length);
    }

    /** {@code ￥} and {@code 𠮷}, and the two ends of each range. Every pair here is one the units
     *  put the other way round. */
    private static final List<List<String>> APART = List.of(
            List.of(text(0xFFE5), text(0x20BB7)),
            List.of(text(0xE000), text(0x10000)),
            List.of(text(0xFFFF), text(0x10FFFF)),
            List.of("a" + text(0xFFE5), "a" + text(0x20BB7)));

    /** Pairs the two orders agree on, so a place answering the reverse of both is caught too. */
    private static final List<List<String>> ALIKE = List.of(
            List.of("a", "b"),
            List.of("ab", "b"),
            List.of("", "a"),
            List.of(text(0xD7FF), text(0x10000)));

    private static List<List<String>> pairs() {
        List<List<String>> out = new ArrayList<>(APART);
        out.addAll(ALIKE);
        return out;
    }

    /** The pairs say something: each of the first kind is one the units order the other way. */
    @Test
    void thePairsTellTheTwoOrdersApart() {
        for (List<String> pair : APART) {
            assertTrue(Strings.compare(pair.get(0), pair.get(1)) < 0, shown(pair));
            assertTrue(pair.get(0).compareTo(pair.get(1)) > 0, shown(pair));
        }
        for (List<String> pair : ALIKE) {
            assertTrue(Strings.compare(pair.get(0), pair.get(1)) < 0, shown(pair));
            assertTrue(pair.get(0).compareTo(pair.get(1)) < 0, shown(pair));
        }
    }

    private static final String MODULE = """
            module demo

            data Code = String
            data In = { a: String, b: String }
            data Out = {
                lt: Bool, le: Bool, gt: Bool, ge: Bool,
                sorted: List<String>, least: String, most: String, byKey: List<String>,
                codeLt: Bool, codes: List<Code>, bag: Set<String>
            }

            behavior run : (i: In) -> Out constructs Out, Code

            let run (i) = Out {
                lt = i.a < i.b,
                le = i.a <= i.b,
                gt = i.a > i.b,
                ge = i.a >= i.b,
                sorted = List.sort([ i.b, i.a ]),
                least = match List.min([ i.b, i.a ]) with | None -> "" | Some m -> m,
                most = match List.max([ i.a, i.b ]) with | None -> "" | Some m -> m,
                byKey = List.sortBy(s -> s, [ i.b, i.a ]),
                codeLt = Code(i.a) < Code(i.b),
                codes = List.sort([ Code(i.b), Code(i.a) ]),
                bag = Set.fromList([ i.b, i.a ])
            }
            """;

    /** {@link #MODULE}, compiled once for the two tests that ask it. */
    private static BytesClassLoader compiled;

    private static synchronized BytesClassLoader module() throws Exception {
        if (compiled == null) {
            compiled = new BytesClassLoader(Compiler.compile(MODULE),
                    TextIsOrderedByScalarValueWhereverItIsOrderedTest.class.getClassLoader());
        }
        return compiled;
    }

    /** What a model says of each pair, both ways round, is what the comparison says. */
    @Test
    void aModelOrdersTextAsTheComparisonDoes() throws Exception {
        BytesClassLoader loader = module();
        Object behavior = Emitted.behavior(loader, "demo", "run").getConstructor().newInstance();
        for (List<String> pair : pairs()) {
            for (List<String> asked : List.of(pair, pair.reversed())) {
                String a = asked.get(0);
                String b = asked.get(1);
                int expected = Strings.compare(a, b);
                String low = expected < 0 ? a : b;
                String high = expected < 0 ? b : a;
                Object in = Codecs.decoded(loader, "demo.In", Map.of("a", a, "b", b));
                Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Out",
                        Codecs.apply(behavior, in));
                String about = shown(asked);
                assertEquals(expected < 0, out.get("lt"), "< over " + about);
                assertEquals(expected <= 0, out.get("le"), "<= over " + about);
                assertEquals(expected > 0, out.get("gt"), "> over " + about);
                assertEquals(expected >= 0, out.get("ge"), ">= over " + about);
                assertEquals(List.of(low, high), out.get("sorted"), "List.sort over " + about);
                assertEquals(low, out.get("least"), "List.min over " + about);
                assertEquals(high, out.get("most"), "List.max over " + about);
                assertEquals(List.of(low, high), out.get("byKey"), "List.sortBy over " + about);
                assertEquals(expected < 0, out.get("codeLt"), "< on a newtype over " + about);
                assertEquals(List.of(low, high), out.get("codes"),
                        "List.sort on a newtype over " + about);
                assertEquals(List.of(low, high), out.get("bag"),
                        "the order a set is written in, over " + about);
            }
        }
    }

    /** What a newtype over text declares to a Java reader, {@code compareTo}, is the same order. */
    @Test
    void aNewtypeOverTextComparesAsTheComparisonDoes() throws Exception {
        BytesClassLoader loader = module();
        for (List<String> pair : pairs()) {
            @SuppressWarnings("unchecked")
            Comparable<Object> a = (Comparable<Object>) Codecs.decoded(loader, "demo.Code", pair.get(0));
            Object b = Codecs.decoded(loader, "demo.Code", pair.get(1));
            assertTrue(a.compareTo(b) < 0, "Code.compareTo over " + shown(pair));
        }
    }

    /** The order a boundary writes in, and the lines and runs the compiler reads a rule by. */
    @Test
    void theBoundaryAndTheCompilerOrderTextAsTheComparisonDoes() {
        for (List<String> pair : pairs()) {
            String a = pair.get(0);
            String b = pair.get(1);
            String about = shown(pair);
            assertTrue(Representations.compareExternalForms(a, b) < 0,
                    "the order a boundary writes in, over " + about);
            assertTrue(Representations.compareExternalForms(Map.of(a, 0L), Map.of(b, 0L)) < 0,
                    "an object by its keys, over " + about);
            // Read in ascending key order, the first member decides: `a` is read first, and 1 is
            // above 0. Read the other way round, `b` would decide, and 0 is below 1.
            assertTrue(Representations.compareExternalForms(Map.of(a, 1L, b, 0L),
                            Map.of(a, 0L, b, 1L)) > 0,
                    "an object's members read in key order, over " + about);
            assertTrue(Text.of(a).compareTo(Text.of(b)) < 0,
                    "where a line is drawn, over " + about);
            Language beforeB = Language.before(b, PatternPlan.Budget.OF_AN_ORDERED_EXTENT.meter());
            assertNotNull(beforeB, about);
            assertTrue(beforeB.has(a), "what comes before, over " + about);
            Language beforeA = Language.before(a, PatternPlan.Budget.OF_AN_ORDERED_EXTENT.meter());
            assertNotNull(beforeA, about);
            assertFalse(beforeA.has(b), "what comes before, over " + about);
            Language both = Language.ofWords(List.of(b, a),
                    PatternPlan.Budget.OF_AN_ORDERED_EXTENT.meter());
            assertNotNull(both, about);
            assertEquals(a, both.least(), "the least of a rule's values, over " + about);
        }
    }

    private static String shown(List<String> pair) {
        List<String> out = new ArrayList<>();
        for (String each : pair) {
            StringBuilder one = new StringBuilder("\"");
            each.codePoints().forEach(cp -> one.append(String.format("U+%04X ", cp)));
            out.add(one.append('"').toString());
        }
        return out.toString();
    }
}
