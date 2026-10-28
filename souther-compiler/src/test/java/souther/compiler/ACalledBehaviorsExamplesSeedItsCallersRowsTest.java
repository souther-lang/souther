package souther.compiler;

import souther.compiler.partition.FixtureTemplate;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.query.RowWork;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule given its own behavior and rows is offered to its caller the way the same rule written
 * as a helper is: as the inputs its rows give.
 */
class ACalledBehaviorsExamplesSeedItsCallersRowsTest {

    private static final String PREFIX = """
            module repro.split

            data Pin = Int
                invariant value >= 1 && value <= 12

            data Throw = List<Pin>
                invariant List.allDistinctBy(p -> p, value)

            """;

    private static final String BODY = """
            let points (t) = {
                let n = List.length(t.value)
                if n == 1 then List.sum(List.map(p -> p.value, t.value)) else n
            }

            """;

    private static final String SCORE = """
            behavior score : (throws: List<Throw>) -> Int

            let score (throws) = List.fold((acc, t) -> acc + points(t), 0, throws)
            """;

    private static final String AS_BEHAVIOR = PREFIX + """
            behavior points : (t: Throw) -> Int

            """ + BODY + """
            example points
                | (Throw([])) -> 0
                | (Throw([Pin(12)])) -> 12
                | (Throw([Pin(1), Pin(2)])) -> 2
                | (Throw([Pin(1), Pin(2), Pin(3)])) -> 3

            """ + SCORE;

    private static final String AS_HELPER = PREFIX + """
            let points (t: Throw): Int = {
                let n = List.length(t.value)
                if n == 1 then List.sum(List.map(p -> p.value, t.value)) else n
            }

            """ + SCORE;

    @Test
    void theRowsOfACalledBehaviorAreInputsOfItsCaller() {
        List<String> offered = offeredForScore(AS_BEHAVIOR);
        for (String throwText : List.of("Throw([])", "Throw([Pin(12)])",
                "Throw([Pin(1), Pin(2)])", "Throw([Pin(1), Pin(2), Pin(3)])")) {
            assertTrue(offered.contains("[" + throwText + "]"),
                    () -> "a list holding " + throwText + " is offered: " + offered);
        }
        assertEquals(offered.stream().distinct().toList(), offered,
                "a row a seed and the fill both arrive at is offered once");
    }

    @Test
    void aHelperIsOfferedTheSameInputs() {
        List<String> offered = offeredForScore(AS_HELPER);
        for (String throwText : List.of("Throw([])", "Throw([Pin(12)])",
                "Throw([Pin(1), Pin(2)])", "Throw([Pin(1), Pin(2), Pin(3)])")) {
            assertTrue(offered.contains("[" + throwText + "]"),
                    () -> "a list holding " + throwText + " is offered: " + offered);
        }
    }

    @Test
    void aCalleeWithNoRowsSeedsNothing() {
        String withoutRows = PREFIX + """
                behavior points : (t: Throw) -> Int

                """ + BODY + SCORE;
        assertEquals(List.of("[]"), offeredForScore(withoutRows));
    }

    @Test
    void theRowsOfTheCalleeAddNoObligationToTheCaller() {
        // Rows that reach the same lines of the declarations, so that what the rows of points
        // meet is the same and the only difference is the inputs they give score.
        String oneRow = PREFIX + """
                behavior points : (t: Throw) -> Int

                """ + BODY + """
                example points
                    | (Throw([Pin(12)])) -> 12

                """ + SCORE;
        String moreRows = PREFIX + """
                behavior points : (t: Throw) -> Int

                """ + BODY + """
                example points
                    | (Throw([Pin(12)])) -> 12
                    | (Throw([])) -> 0
                    | (Throw([Pin(5), Pin(7)])) -> 2

                """ + SCORE;
        assertTrue(offeredForScore(moreRows).contains("[Throw([Pin(5), Pin(7)])]")
                        && !offeredForScore(oneRow).contains("[Throw([Pin(5), Pin(7)])]"),
                "the rows differ in what they seed");
        RowWork few = owedForScore(oneRow);
        RowWork many = owedForScore(moreRows);
        assertEquals(few.classes(), many.classes(), "classes");
        assertEquals(few.arms(), many.arms(), "arms");
        assertEquals(few.pairs(), many.pairs(), "pairs");
        assertEquals(few.meetings(), many.meetings(), "meetings");
        assertEquals(few.rules(), many.rules(), "rules");
        assertEquals(few.replacements(), many.replacements(), "replacements");
        assertEquals(few.cases(), many.cases(), "cases");
        // The lines the declarations draw are owed to every behavior that carries their type, and
        // a row of points that reaches one meets it for score too. That is what rows reaching
        // lines do whoever calls whom; a point owed with more rows is a point owed because of them.
        assertTrue(few.points().stream().map(each -> each.point()).toList().containsAll(
                many.points().stream().map(each -> each.point()).toList()),
                "more rows of points owe score no point fewer rows did not");
    }

    @Test
    void theSameRowsAreOfferedInTheSameOrderEachTime() {
        assertEquals(offeredForScore(AS_BEHAVIOR), offeredForScore(AS_BEHAVIOR));
    }

    private static final String ADD = """
            module repro.add

            behavior add : (x: Int, y: Int) -> Int

            let add (x, y) = x + y

            example add
                | (3, 7) -> 10

            """;

    @Test
    void aRowOfTheCalleeIsSeededWholeOrNotAtAll() {
        String constantSecond = ADD + """
                behavior score : (x: Int) -> Int

                let score (x) = add(x, 0)
                """;
        assertEquals(List.of(), seededOnly(constantSecond, "repro.add", "score"),
                "score(3) calls add(3, 0), which is no row of add");
    }

    @Test
    void aCallerThatOwesNothingIsSeededAtEveryInputAThrough() {
        String joined = """
                module repro.join

                behavior join : (a: String, b: String) -> String

                let join (a, b) = String.append(a, b)

                example join
                    | ("x", "y") -> "xy"

                behavior wrapper : (a: String, b: String) -> String

                let wrapper (a, b) = join(a, b)
                """;
        assertTrue(offered(joined, "repro.join", "wrapper").contains("\"x\", \"y\""),
                () -> "join's row is wrapper's: " + offered(joined, "repro.join", "wrapper"));
    }

    /** A caller that depends on another behavior, and calls one that has rows. */
    private static final String WITH_A_DEPENDENCY = """
            module repro.dep

            behavior scale : (n: Int) -> Int

            let scale (n) = n + 1

            example scale
                | (5) -> 6

            behavior rate : (n: Int) -> Int

            fake rate
                | _ -> 2

            behavior total : (xs: List<Int>) -> Int
                depends on rate

            let total (xs, rate) = List.fold((acc, x) -> acc + scale(x) + rate(x), 0, xs)
            """;

    @Test
    void aSeededRowStandsInEveryDependencyItsCallerRequires() {
        Compilation compilation = Compilation.ofSource(WITH_A_DEPENDENCY, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList(),
                "the model compiles");
        var offering = Adequacy.offeredFor(compilation.db(),
                OfferingRequest.overTheModule("repro.dep"));
        var rows = offering.rowsByBehavior().getOrDefault("total", List.of());
        var seeded = rows.stream()
                .filter(row -> row.inputs().stream().anyMatch(each -> each.text().equals("[5]")))
                .toList();
        assertEquals(1, seeded.size(), () -> "scale's row is total's: " + rows);
        assertEquals(1, seeded.getFirst().answers().size(),
                "and total's dependency is answered in it, as it is in every row");
    }

    @Test
    void oneInputHandedToTwoArgumentsIsSeededWhenTheRowGivesThemTheSameValue() {
        String twice = ADD.replace("(3, 7) -> 10", "(3, 3) -> 6") + """
                behavior double : (x: Int) -> Int

                let double (x) = add(x, x)
                """;
        assertEquals(List.of("3"), seededOnly(twice, "repro.add", "double"),
                "double(3) calls add(3, 3), which is add's row");
        String apart = ADD + """
                behavior double : (x: Int) -> Int

                let double (x) = add(x, x)
                """;
        assertEquals(List.of(), seededOnly(apart, "repro.add", "double"),
                "no value of x is both 3 and 7");
    }

    @Test
    void aRowOfTheCalleeIsSeededWhenEveryArgumentStandsAtAnInput() {
        String wrapper = ADD + """
                behavior wrapper : (a: Int, b: Int) -> Int

                let wrapper (a, b) = add(a, b)
                """;
        assertTrue(offered(wrapper, "repro.add", "wrapper").contains("3, 7"),
                () -> "add's row is wrapper's: " + offered(wrapper, "repro.add", "wrapper"));
    }

    /** What a row of score is owed for, as the generation asks it. */
    private static RowWork owedForScore(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation.db().ask(new Adequacy.RowsOwed("repro.split", "score")).value();
    }

    private static List<String> offeredForScore(String source) {
        return offered(source, "repro.split", "score");
    }

    private static List<String> offered(String source, String module, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule(module))
                .rowsByBehavior().getOrDefault(behavior, List.of()).stream()
                .map(row -> String.join(", ",
                        row.inputs().stream().map(FixtureTemplate::text).toList()))
                .toList();
    }

    /** The rows offered that the fill alone would not offer: what the callees' rows add. */
    private static List<String> seededOnly(String source, String module, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation.db().ask(new Adequacy.Generated(module, behavior)).value()
                .callSeeds().stream()
                .map(row -> String.join(", ",
                        row.inputs().stream().map(FixtureTemplate::text).toList()))
                .toList();
    }
}
