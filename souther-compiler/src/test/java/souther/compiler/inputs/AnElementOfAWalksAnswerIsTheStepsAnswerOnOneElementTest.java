package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.UndividedPosition;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An element of what a walk answering one value per element holds is the walk's step on one
 * element, and a rule about it is a rule about that.
 *
 * <p>{@code List.filter(c -> c >= atLeast, List.map(x -> x + 1, cs))} states {@code cs[*] + 1 >=
 * atLeast}, and the line it draws is on {@code cs[*]} one below {@code atLeast}. Which step it is
 * is read off the application that built the container, so two walks over one list are two
 * different rules — and an operation that does not answer one value per element, a set's
 * {@code map}, leaves its element an element and no more.
 *
 * <p>Where the element is left that way, the rule is still filed where its values came from, beside
 * the place it was filed at. That place keeps its own word: what a position whose values the rule
 * is about is left with is that position's, and is not changed by where the other side came from.
 */
class AnElementOfAWalksAnswerIsTheStepsAnswerOnOneElementTest {

    @Test
    void anElementOfAListsMapIsTheStepOnOneElement() {
        assertEquals(List.of("cs[*] = atLeast - 1"), linesOf("""
                behavior busy : (cs: List<Int>, atLeast: Int) -> List<Int>
                let busy (cs, atLeast) = List.filter(c -> c >= atLeast, List.map(x -> x + 1, cs))
                """));
    }

    @Test
    void aValueOfAMapsMappedValuesIsTheStepOnTheValueFiledThere() {
        assertEquals(List.of("m[*] = atLeast - 1"), linesOf("""
                behavior busy : (m: Map<String, Int>, atLeast: Int) -> Map<String, Int>
                let busy (m, atLeast) =
                    Map.filterEntries((_, count) -> count >= atLeast,
                        Map.mapValues((_, v) -> v + 1, m))
                """));
    }

    /** A step that is no arithmetic is read as whatever the reading of a number makes of it. */
    @Test
    void aStepIsReadAsAnyExpressionIs() {
        assertEquals(List.of("String.length(xs[*]) = atLeast"), linesOf("""
                behavior busy : (xs: List<String>, atLeast: Int) -> List<Int>
                let busy (xs, atLeast) =
                    List.filter(c -> c >= atLeast, List.map(x -> String.length(x), xs))
                """));
    }

    /** Two walks over one list are told apart by the application, and not by the list. */
    @Test
    void twoWalksOverOneListAreTwoSteps() {
        String model = """
                behavior busy : (cs: List<Int>, atLeast: Int) -> List<Int>
                let busy (cs, atLeast) = {
                    let a = List.map(x -> x + 1, cs)
                    let b = List.map(x -> x + 10, cs)
                    List.append(FIRST, SECOND)
                }
                """;
        assertEquals(List.of("cs[*] = atLeast - 1"), linesOf(model
                .replace("FIRST", "List.filter(c -> c >= atLeast, a)").replace("SECOND", "b")));
        assertEquals(List.of("cs[*] = atLeast - 10"), linesOf(model
                .replace("FIRST", "a").replace("SECOND", "List.filter(c -> c >= atLeast, b)")));
    }

    @Test
    void aWalkOverAWalkIsOneStepAfterTheOther() {
        assertEquals(List.of("-atLeast + 2 * cs[*] = -2"), linesOf("""
                behavior busy : (cs: List<Int>, atLeast: Int) -> List<Int>
                let busy (cs, atLeast) =
                    List.filter(c -> c >= atLeast, List.map(y -> y * 2, List.map(x -> x + 1, cs)))
                """));
    }

    /**
     * A set's {@code map} may answer one value for two elements, so an element of its answer is no
     * step on any one of them: no line, the rule filed at where the values came from, and the
     * position the rule is about left with its own word.
     */
    @Test
    void aWalkThatAnswersNoValuePerElementLeavesAnElement() {
        String model = """
                behavior busy : (cs: Set<Int>, atLeast: Int) -> Set<Int>
                let busy (cs, atLeast) = Set.filter(c -> c >= atLeast, Set.map(x -> x + 1, cs))
                """;
        assertEquals(List.of(), linesOf(model));
        List<String> notRead = notReadIn(model);
        assertTrue(notRead.contains("cs[*] " + UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE),
                () -> "filed where the values came from: " + notRead);
        assertEquals(List.of("atLeast " + UndividedPosition.Reason.UNSUPPORTED_SYNTAX),
                notRead.stream().filter(each -> each.startsWith("atLeast ")).toList(),
                "and the position the rule is about keeps its own word");
    }

    /**
     * A count a fold worked out is no step on an element of the list folded, and where it came from
     * is not said here: the position it is compared with keeps its own word and is told nothing
     * about a value made from it.
     */
    @Test
    void aValueAFoldWorkedOutIsNoStep() {
        String model = """
                let countsOf (xs: List<String>): Map<String, Int> =
                    List.fold((acc, x) -> Map.updateOrInsert(x, 1, n -> n + 1, acc), Map.empty, xs)

                behavior busy : (xs: List<String>, atLeast: Int) -> Map<String, Int>
                let busy (xs, atLeast) =
                    Map.filterEntries((_, count) -> count >= atLeast, countsOf(xs))
                """;
        assertEquals(List.of(), linesOf(model));
        List<String> notRead = notReadIn(model);
        assertEquals(List.of("atLeast " + UndividedPosition.Reason.UNSUPPORTED_SYNTAX),
                notRead.stream().filter(each -> each.startsWith("atLeast ")).toList(),
                () -> "the position the rule is about keeps its own word: " + notRead);
    }

    /** Every line the comparison in {@code body} draws, as its label. */
    private static List<String> linesOf(String body) {
        Compilation compilation = compiled(body);
        return Adequacy.readingsOf(compilation.db(), "probe").get("busy").stream()
                .map(BorderAssessment::label)
                .toList();
    }

    /** Every place the rules of {@code body} were not read at, with the reason. */
    private static List<String> notReadIn(String body) {
        PartitionEvidence measured = compiled(body).db()
                .ask(new Adequacy.Coverage("probe")).value().get("busy");
        return measured.notRead().stream()
                .map(each -> each.at() + " " + each.reason())
                .toList();
    }

    private static Compilation compiled(String body) {
        Compilation compilation = Compilation.ofSource("module probe\n\n" + body, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model compiles");
        return compilation;
    }
}
