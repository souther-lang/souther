package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Located;
import souther.compiler.query.Compilation;
import souther.test.Nightly;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the discharge of a rule takes a guard over a library operation to settle is what the
 * operation does when it is run.
 *
 * <p>Each row is a data type whose invariant is {@code value >= 0}, constructed from a number that
 * is a count of something less a constant, under a guard that holds or is denied. The discharge
 * owes it something or it does not; a row it owes nothing is one it has proved, and no input
 * satisfying the guard may then break the invariant when the compiled module is run. The rows it
 * owes are the control: some input breaks each guard's rows, so that the inputs reach the cases
 * the guard separates and a row passing is not a row never run.
 *
 * <p>This holds the readings of the library's laws to the operations themselves. Every other test
 * of them states what a law says; this one asks the operation.
 */
@Nightly
class WhatTheDischargeSettlesOfALibraryOperationIsWhatTheRunHoldsTest {

    private static final List<String> GUARDS = List.of(
            "List.any(n -> n > 2, xs)",
            "List.all(n -> n > 2, xs)",
            "List.contains(x, xs)",
            "List.length(xs) >= 1",
            "List.allDistinctBy(n -> n, xs)",
            "Set.contains(x, a)",
            "Set.size(a) >= 1",
            "String.startsWith(\"JP\", s)",
            "String.contains(t, s)",
            "String.endsWith(t, s)",
            "String.length(String.trim(s)) >= 1",
            "String.length(s ++ t) >= 2",
            "List.length(List.concat(xss)) >= 1",
            "List.any(n -> n > 2, List.filter(n -> n > 1, xs))",
            "List.length(List.filter(n -> n > 2, xs)) >= 2",
            "List.length(List.filter(n -> n > 2, xs)) == List.length(xs)",
            "List.all(n -> n <= 2, xs)",
            "List.any(n -> n <= 2, xs)",
            "Set.size(Set.union(a, b)) >= 2",
            "Set.size(Set.intersection(a, b)) >= 1",
            "Set.size(Set.difference(a, b)) >= 1",
            "Set.contains(x, Set.difference(a, b))",
            "List.any(ys -> List.length(ys) >= 2, xss)",
            "List.length(List.distinct(xs)) >= 2",
            "Map.size(List.groupBy(n -> n, xs)) >= 2",
            "List.sum(xs) >= 3",
            "List.sum(xs) > 0",
            "List.fold((acc, n) -> acc + n, 5, xs) > 5",
            "List.length(List.flatMap(n -> [n, n], xs)) >= 2",
            "Set.size(Set.fromList(xs)) >= 2");

    private static final List<String> COUNTS = List.of(
            "List.length(xs)",
            "List.length(List.filter(n -> n > 2, xs))",
            "List.length(List.filter(n -> n <= 2, xs))",
            "List.length(List.distinct(xs))",
            "List.length(List.distinctBy(n -> n, xs))",
            "Set.size(a)",
            "Set.size(b)",
            "Set.size(Set.union(a, b))",
            "Set.size(Set.difference(a, b))",
            "Set.size(Set.intersection(a, b))",
            "Set.size(Set.fromList(xs))",
            "List.length(List.concat(xss))",
            "List.length(xss)",
            "String.length(s)",
            "String.length(t)",
            "String.length(String.trim(s))",
            "Map.size(List.groupBy(n -> n, xs))",
            "List.length(List.reverse(xs))",
            "List.length(List.flatMap(n -> [n, n], xs))",
            "Set.size(Set.remove(x, a))",
            "Set.size(Set.insert(x, a))",
            "List.length(List.append(xs, xs))");

    /** The arguments a guard and a count are written over, read off the one input they are run
     *  with. */
    private static final Pattern ARGUMENT = Pattern.compile("\\b(xss|xs|a|b|s|t|x)\\b(?![\"(])");

    private static final String INPUT = """
            module demo

            data In = { xs: List<Int>, xss: List<List<Int>>, a: Set<Int>, b: Set<Int>,
                        s: String, t: String, x: Int }

            """;

    /** One data type, its invariant, and the behavior constructing it. */
    private record Row(int id, String guard, boolean guardHolds, String count, int below) {

        String source() {
            String made = ARGUMENT.matcher(count).replaceAll("i.$1") + " - " + below;
            String guarded = ARGUMENT.matcher(guard).replaceAll("i.$1");
            String body = guardHolds
                    ? "if %s then D%d(%s) else D%d(0)".formatted(guarded, id, made, id)
                    : "if %s then D%d(0) else D%d(%s)".formatted(guarded, id, id, made);
            return """
                    data D%1$d = Int
                        invariant atLeastNought = value >= 0

                    behavior f%1$d : (i: In) -> D%1$d constructs D%1$d
                    let f%1$d (i) = %2$s
                    """.formatted(id, body);
        }

        String data() {
            return "D" + id;
        }
    }

    private static String module(List<Row> rows) {
        StringBuilder out = new StringBuilder(INPUT);
        rows.forEach(each -> out.append(each.source()).append('\n'));
        return out.toString();
    }

    private static final List<String> STRINGS =
            List.of("", "a", " ", "ab", "JP", "JPx", " a ", "xJP", "JP ");

    private static List<Long> ints(Random random, int most) {
        List<Long> out = new ArrayList<>();
        for (int n = random.nextInt(most + 1); n > 0; n--) {
            out.add((long) random.nextInt(5));
        }
        return out;
    }

    /** Inputs drawn the same way every run: lists and sets of small numbers, and strings that
     *  start, end and contain one another and are whitespace. */
    private static List<Map<String, Object>> inputs(int count) {
        Random random = new Random(3085);
        List<Map<String, Object>> out = new ArrayList<>();
        for (int n = 0; n < count; n++) {
            List<List<Long>> xss = new ArrayList<>();
            for (int rows = random.nextInt(4); rows > 0; rows--) {
                xss.add(ints(random, 3));
            }
            Map<String, Object> in = new LinkedHashMap<>();
            in.put("xs", ints(random, 4));
            in.put("xss", xss);
            in.put("a", new ArrayList<>(new LinkedHashSet<>(ints(random, 3))));
            in.put("b", new ArrayList<>(new LinkedHashSet<>(ints(random, 3))));
            in.put("s", STRINGS.get(random.nextInt(STRINGS.size())));
            in.put("t", STRINGS.get(random.nextInt(STRINGS.size())));
            in.put("x", (long) random.nextInt(5));
            out.add(in);
        }
        return out;
    }

    /** What running {@code rows} over {@code inputs} came to, beside what the discharge said. */
    private record Judged(Set<String> owed, Set<String> broke) {

        Set<String> provedAndBroke() {
            Set<String> out = new LinkedHashSet<>(broke);
            out.removeAll(owed);
            return out;
        }

        long owedAndBroke() {
            return owed.stream().filter(broke::contains).count();
        }
    }

    private Judged judged(List<Row> rows, List<Map<String, Object>> inputs) throws Exception {
        Compilation compilation = Compilation.ofSource(module(rows), "Main");
        compilation.answerEverything();
        Set<String> owed = new LinkedHashSet<>();
        Set<String> refused = new LinkedHashSet<>();
        for (Located each : compilation.errors()) {
            assertEquals("E2010", each.diagnostic().code(), () -> "a row compiles: " + each);
            refused.add(String.valueOf(each.diagnostic().values().get("data")));
        }
        for (Located each : compilation.warnings()) {
            if ("E2011".equals(each.diagnostic().code())) {
                owed.add(String.valueOf(each.diagnostic().values().get("data")));
            }
        }
        // A row refused is a violation the discharge is sure of, and the module is not built.
        List<Row> built = rows.stream().filter(each -> !refused.contains(each.data())).toList();
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(module(built)),
                getClass().getClassLoader());
        Set<String> broke = new LinkedHashSet<>();
        for (Row row : built) {
            Object behavior = Emitted.behavior(loader, "demo", "f" + row.id())
                    .getConstructor().newInstance();
            for (Map<String, Object> input : inputs) {
                try {
                    Codecs.apply(behavior, Codecs.decoded(loader, "demo.In", input));
                } catch (Throwable thrown) {
                    // An operation that aborts, such as a slice out of range, is not the invariant
                    // breaking; it names the data when it is.
                    if (thrown.getClass().getSimpleName().equals("ConstraintViolation")
                            && String.valueOf(thrown.getMessage()).contains(row.data())) {
                        broke.add(row.data());
                        break;
                    }
                    if (!thrown.getClass().getSimpleName().equals("ConstraintViolation")) {
                        throw thrown;
                    }
                }
            }
        }
        owed.addAll(refused);
        return new Judged(owed, broke);
    }

    @Test
    void whatIsProvedUnderAGuardHoldsOfEveryInputThatSatisfiesIt() throws Exception {
        List<Map<String, Object>> inputs = inputs(600);
        List<String> unsound = new ArrayList<>();
        List<String> unreached = new ArrayList<>();
        int id = 0;
        for (String guard : GUARDS) {
            for (boolean holds : new boolean[] {true, false}) {
                List<Row> rows = new ArrayList<>();
                for (String count : COUNTS) {
                    for (int below = 0; below <= 2; below++) {
                        rows.add(new Row(id++, guard, holds, count, below));
                    }
                }
                Judged judged = judged(rows, inputs);
                for (Row row : rows) {
                    if (judged.provedAndBroke().contains(row.data())) {
                        unsound.add((holds ? "" : "not ") + guard + ": " + row.count() + " - "
                                + row.below());
                    }
                }
                if (judged.owedAndBroke() == 0) {
                    unreached.add((holds ? "" : "not ") + guard);
                }
            }
        }
        assertEquals(List.of(), unsound, "proved, and broken by an input");
        // A guard that no input separates the rows of is one nothing was asked of.
        assertTrue(unreached.isEmpty(), () -> "guards no input breaks a row of: " + unreached);
    }

    @Test
    void whatIsProvedOfOneCountAgainstAnotherHoldsOfEveryInput() throws Exception {
        List<Map<String, Object>> inputs = inputs(600);
        List<String> unsound = new ArrayList<>();
        int id = 100_000;
        for (String left : COUNTS) {
            List<Row> rows = new ArrayList<>();
            for (String right : COUNTS) {
                if (!left.equals(right)) {
                    for (int below = 0; below <= 1; below++) {
                        rows.add(new Row(id++, "true", true, left + " - " + right, below));
                    }
                }
            }
            Judged judged = judged(rows, inputs);
            for (Row row : rows) {
                if (judged.provedAndBroke().contains(row.data())) {
                    unsound.add(row.count() + " - " + row.below());
                }
            }
        }
        assertEquals(List.of(), unsound, "proved, and broken by an input");
    }
}
