package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.Located;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What the library proves of two operations answering over the same arguments is read by the
 * check of a construction: the sizes of the answers are one number each, tied by the relation, so
 * a difference of them that the relation settles at nought is not owed a row.
 */
class TheSizesOfTwoAnswersOverTheSameArgumentsAreRelatedTest {

    private static final String INPUT = """
            module demo

            data In = { xs: List<Int>, ys: List<Int>, x: Int, a: Set<Int>, b: Set<Int> }

            """;

    /** One data type held to at-or-above nought, and the behavior constructing it of {@code count}. */
    private record Row(int id, String count) {

        String source() {
            return """
                    data D%1$d = Int
                        invariant atLeastNought = value >= 0

                    behavior f%1$d : (i: In) -> D%1$d constructs D%1$d
                    let f%1$d (i) = D%1$d(%2$s)
                    """.formatted(id, count);
        }

        String data() {
            return "D" + id;
        }
    }

    /** The rows whose construction is owed a row or refused. */
    private static Set<String> notProved(List<Row> rows) {
        StringBuilder module = new StringBuilder(INPUT);
        rows.forEach(each -> module.append(each.source()).append('\n'));
        Compilation compilation = Compilation.ofSource(module.toString(), "Main");
        compilation.answerEverything();
        Set<String> out = new LinkedHashSet<>();
        List<Located> found = new ArrayList<>(compilation.errors());
        found.addAll(compilation.warnings());
        for (Located each : found) {
            if ("E2010".equals(each.diagnostic().code())
                    || "E2011".equals(each.diagnostic().code())) {
                out.add(String.valueOf(each.diagnostic().values().get("data")));
            }
        }
        return out;
    }

    private static final String TAKEN_AND_DROPPED =
            "List.length(List.take(i.x, i.xs)) + List.length(List.drop(i.x, i.xs))";

    private static final String PAIRED = "List.length(List.zipShortest(i.xs, i.ys))";

    private static final String PAIRED_SWAPPED = "List.length(List.zipShortest(i.ys, i.xs))";

    @Test
    void whatIsTakenAndWhatIsDroppedAreTheWholeList() {
        List<Row> proved = List.of(
                new Row(1, TAKEN_AND_DROPPED + " - List.length(i.xs)"),
                new Row(2, "List.length(i.xs) - (" + TAKEN_AND_DROPPED + ")"),
                new Row(3, "List.length(List.take(2, i.xs)) + List.length(List.drop(2, i.xs))"
                        + " - List.length(i.xs)"),
                new Row(4, "List.length(List.drop(i.x, i.xs)) + List.length(List.take(i.x, i.xs))"
                        + " - List.length(i.xs)"));
        assertEquals(Set.of(), notProved(proved));
    }

    @Test
    void whatIsTakenAndDroppedIsNotMoreOrLessThanTheWholeList() {
        List<Row> notProved = List.of(
                new Row(11, TAKEN_AND_DROPPED + " - List.length(i.xs) - 1"),
                new Row(12, "List.length(i.xs) - (" + TAKEN_AND_DROPPED + ") - 1"),
                new Row(13, "List.length(List.take(i.x, i.xs)) + List.length(List.drop(i.x, i.ys))"
                        + " - List.length(i.xs)"),
                new Row(14, "List.length(List.take(i.x, i.xs)) + List.length(List.drop(2, i.xs))"
                        + " - List.length(i.xs)"));
        assertEquals(Set.of("D11", "D12", "D13", "D14"), notProved(notProved));
    }

    @Test
    void twoListsPairedEitherWayRoundAreAsLongAsEachOther() {
        List<Row> proved = List.of(
                new Row(21, PAIRED + " - " + PAIRED_SWAPPED),
                new Row(22, PAIRED_SWAPPED + " - " + PAIRED));
        assertEquals(Set.of(), notProved(proved));
    }

    @Test
    void aValuePutInOrTakenOutIsAsManyAsTheUnionOrTheDifferenceWithItAlone() {
        List<Row> proved = List.of(
                new Row(41, "Set.size(Set.insert(i.x, i.a)) - Set.size(Set.union(i.a,"
                        + " Set.singleton(i.x)))"),
                new Row(42, "Set.size(Set.union(i.a, Set.singleton(i.x)))"
                        + " - Set.size(Set.insert(i.x, i.a))"),
                new Row(43, "Set.size(Set.remove(i.x, i.a)) - Set.size(Set.difference(i.a,"
                        + " Set.singleton(i.x)))"),
                new Row(44, "Set.size(Set.difference(i.a, Set.singleton(i.x)))"
                        + " - Set.size(Set.remove(i.x, i.a))"));
        assertEquals(Set.of(), notProved(proved));
    }

    @Test
    void aValuePutInIsNotAsManyAsAUnionWithAnotherSetOrValue() {
        List<Row> notProved = List.of(
                new Row(51, "Set.size(Set.insert(i.x, i.a)) - Set.size(Set.union(i.a,"
                        + " Set.singleton(i.x))) - 1"),
                new Row(52, "Set.size(Set.insert(i.x, i.a)) - Set.size(Set.union(i.b,"
                        + " Set.singleton(i.x)))"),
                new Row(53, "Set.size(Set.insert(i.x, i.a)) - Set.size(Set.union(i.a,"
                        + " Set.singleton(i.x + 1)))"),
                new Row(54, "Set.size(Set.remove(i.x, i.a)) - Set.size(Set.difference(i.b,"
                        + " Set.singleton(i.x)))"));
        assertEquals(Set.of("D51", "D52", "D53", "D54"), notProved(notProved));
    }

    @Test
    void twoListsPairedAreNotLongerThanTheSwappedPairingByAnything() {
        List<Row> notProved = List.of(
                new Row(31, PAIRED + " - " + PAIRED_SWAPPED + " - 1"),
                new Row(32, "List.length(List.zipShortest(i.xs, i.xs)) - " + PAIRED_SWAPPED));
        assertEquals(Set.of("D31", "D32"), notProved(notProved));
    }
}
