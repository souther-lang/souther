package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.GenerationOutcome;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A decision rule whose condition compares what the elements of a container add up to is composed
 * a row the way a point of the same comparison is: a container whose elements come to a total the
 * condition admits, beside whatever else the way to the rule fixes.
 *
 * <p>Held by running the rows. Each row composed for a rule is put back as an example, answered
 * with what the condition works out to over the numbers the row holds — read here, apart from
 * anything the compiler read — so a row standing short of its rule, or a total the composing got
 * wrong, is an example the model answers otherwise.
 *
 * <p>And a number the rules leave a value is not always one some input comes to: a list of three
 * elements each at least five adds up to no ten. A total chosen where nothing composes is passed
 * over for one that does, and a condition whose every number nothing composes is the one condition
 * the row is composed without.
 */
class ARuleOverATotalOfTheElementsIsComposedAContainerComingToItTest {

    /** A field of each element added up, of a list the rules make hold three, beside a number of
     *  each element the total does not read. */
    private static final String A_FIELD = """
            module p
            data Line = { sku: String, q: Int, discount: Int }
            data Lines = List<Line>
                invariant several = List.length(value) >= 3
            behavior pick : (ls: Lines) -> Int
            let pick (ls) =
                if List.sum(List.map(l -> l.q, ls.value)) >= 10 then 1 else 0
            """;

    /** The leaves of a list of lists added up. */
    private static final String LISTS_OF_A_LIST = """
            module p
            data Posting = { q: Int }
            data Entry = { postings: List<Posting> }
            data Ledger = { entries: List<Entry> }
            behavior pick : (ledger: Ledger) -> Int
            let pick (ledger) =
                if List.sum(List.map(p -> p.q, List.flatMap(.postings, ledger.entries))) >= 10
                then 1 else 0
            """;

    /** A total held between two ends, which is one demand on it and not two. */
    private static final String BETWEEN = """
            module p
            data Line = { q: Int }
            behavior pick : (ls: List<Line>) -> Int
            let pick (ls) = {
                let t = List.sum(List.map(l -> l.q, ls))
                if t >= 10 && t <= 20 then 1 else 0
            }
            """;

    /**
     * Every element at least five and three of them: the least total is fifteen, which the rules
     * of the total itself do not say. The total the condition's own end offers composes nothing,
     * and the one it is passed over for does. Below the condition is a total no list comes to,
     * which no rule of the total says either.
     */
    private static final String A_LEAST_EACH_ELEMENT_HOLDS = """
            module p
            data Line = { q: Int }
                invariant minimum = q >= 5
            data Lines = List<Line>
                invariant several = List.length(value) >= 3
            behavior pick : (ls: Lines) -> Int
            let pick (ls) =
                if List.sum(List.map(l -> l.q, ls.value)) >= 10
                then 1 else 0
            """;

    /**
     * A total added to another parameter, chosen together: the other held at three at the most and
     * every element at least three, three of them. What the pair's first assignment puts the total
     * at composes nothing, and the walk steps on to one that does.
     */
    private static final String BESIDE_ANOTHER = """
            module p
            data Line = { q: Int }
                invariant minimum = q >= 3
            data Lines = List<Line>
                invariant several = List.length(value) >= 3
            behavior pick : (ls: Lines, y: Int) -> Int
            let pick (ls, y) =
                if List.sum(List.map(l -> l.q, ls.value)) + y >= 10 && y <= 3 then 1 else 0
            """;

    /**
     * The same of a number taken of one position: a code two or five long, held to three or more.
     * The length the condition's end offers composes no code the rules keep, and the one past it
     * that does is where every rule below the condition is composed.
     */
    private static final String A_LENGTH_THE_RULES_SKIP = """
            module p
            data Code = String
                invariant two_or_five = String.length(value) == 2 || String.length(value) == 5
            behavior pick : (c: Code, n: Int) -> Int
            let pick (c, n) = {
                guard String.length(c.value) >= 3 else 0
                if n > 3 then 1 else 2
            }
            """;

    /** Each model, with what its condition works out to over the inputs a row holds and the
     *  answers some row of it is composed for. */
    private static final Map<String, Answered> ANSWERED = Map.of(
            A_FIELD, new Answered(row -> totalOf(row.get(0), "q") >= 10 ? 1 : 0, Set.of(0, 1)),
            LISTS_OF_A_LIST, new Answered(row -> totalOf(row.get(0), "q") >= 10 ? 1 : 0,
                    Set.of(0, 1)),
            BETWEEN, new Answered(row -> {
                long total = totalOf(row.get(0), "q");
                return total >= 10 && total <= 20 ? 1 : 0;
            }, Set.of(0, 1)),
            A_LEAST_EACH_ELEMENT_HOLDS, new Answered(
                    row -> totalOf(row.get(0), "q") >= 10 ? 1 : 0, Set.of(1)),
            BESIDE_ANOTHER, new Answered(row -> {
                long y = wholeNumber(row.get(1));
                return totalOf(row.get(0), "q") + y >= 10 && y <= 3 ? 1 : 0;
            }, Set.of(0, 1)),
            A_LENGTH_THE_RULES_SKIP, new Answered(row -> textOf(row.get(0)).length() < 3 ? 0
                    : wholeNumber(row.get(1)) > 3 ? 1 : 2, Set.of(0, 1, 2)));

    /**
     * What a model's condition works out to over a row's inputs, and the answers of the rules a row
     * is composed for — every rule but one whose condition nothing the rules keep meets.
     */
    private record Answered(Function<List<Hir.Expr>, Integer> by, Set<Integer> composedFor) {}

    @Test
    void everyRuleSomeInputTakesIsComposedARowThatTakesIt() {
        ANSWERED.forEach((model, answered) -> {
            List<String> examples = new ArrayList<>();
            Set<Integer> answers = new TreeSet<>();
            for (List<FixtureTemplate> row : composedForTheRules(measured(model))) {
                int answer = answered.by().apply(row.stream().map(FixtureTemplate::value).toList());
                answers.add(answer);
                examples.add("    | \"composed " + examples.size() + "\" : ("
                        + String.join(", ", row.stream().map(FixtureTemplate::text).toList())
                        + ") -> " + answer);
            }
            assertEquals(answered.composedFor(), answers,
                    () -> "a row for every rule some input takes: " + examples);

            Compilation answeredBy = measured(model + "example pick\n"
                    + String.join("\n", examples) + "\n");
            assertEquals(List.of(), answeredBy.errors().stream()
                    .map(each -> each.diagnostic().code() + " " + each.diagnostic().said())
                    .toList(), () -> "each row is answered as its inputs say: " + examples);
        });
    }

    /**
     * And none of them is a rule some input takes whose row was composed without the condition
     * that leads to it: what the condition asks is one of the numbers the row was composed against.
     */
    @Test
    void noRuleSomeInputTakesIsComposedWithoutTheConditionOnTheWayToIt() {
        for (String model : List.of(A_FIELD, LISTS_OF_A_LIST, BETWEEN, BESIDE_ANOTHER,
                A_LENGTH_THE_RULES_SKIP)) {
            String report = report(measured(model));
            assertTrue(report.lines().noneMatch(line ->
                            line.contains("nothing could show a row can be written at")
                                    && line.contains("decision rule")),
                    () -> report);
        }
    }

    /**
     * A total no list the rules keep comes to is the one condition a row past it is composed
     * without, and every point past it is still composed a row.
     *
     * <p>Every element two at the most and three of them: no total reaches ten, though nothing in
     * the rules of the total says so. What is said of the line below the condition is that the row
     * was composed without it — and not that nothing could build a value for the list, which would
     * be the condition taking every other number of the row with it.
     */
    @Test
    void aTotalNothingComposesIsTheOneConditionTheRowIsComposedWithout() {
        String report = report(measured("""
                module p
                data Line = { q: Int }
                    invariant small = q >= 0 && q <= 2
                data Lines = List<Line>
                    invariant few = List.length(value) <= 3
                behavior pick : (ls: Lines, n: Int) -> Int
                let pick (ls, n) = {
                    guard List.sum(List.map(l -> l.q, ls.value)) >= 10 else 0
                    if n > 3 then 1 else 2
                }
                """));
        List<String> past = report.lines().filter(line -> line.contains("read as pick/n:"))
                .toList();

        assertFalse(past.isEmpty(), () -> report);
        for (String line : past) {
            assertTrue(line.contains("not every condition on the way to the line is one the row"
                            + " was composed against: a condition on positions this compiler"
                            + " stopped looking at"),
                    () -> "the row past the condition is composed without it: " + line);
            assertFalse(line.contains("could build a representative"),
                    () -> "and the condition takes nothing else of the row with it: " + line);
        }
    }

    /** The rows composed for the decision rules no row takes, each as its inputs. */
    private static List<List<FixtureTemplate>> composedForTheRules(Compilation compilation) {
        List<List<FixtureTemplate>> out = new ArrayList<>();
        Adequacy.generatedOf(compilation.db(), compilation.modules().get(0)).get("pick")
                .generation().stream()
                .filter(each -> each.finding().about() instanceof About.ARuleNoRowTakes)
                .forEach(each -> {
                    if (each.outcome() instanceof GenerationOutcome.Generated made) {
                        made.candidates().forEach(row -> out.add(row.inputs()));
                    }
                });
        return out;
    }

    /**
     * What the numbers at {@code field} come to, wherever in {@code value} a record holds one: the
     * field the condition reads, and none of the record's others.
     */
    private static long totalOf(Hir.Expr value, String field) {
        return switch (value) {
            case Hir.Apply applied -> applied.args().stream()
                    .mapToLong(each -> totalOf(each, field)).sum();
            case Hir.ListLit list -> list.elements().stream()
                    .mapToLong(each -> totalOf(each, field)).sum();
            case Hir.NewData record -> record.inits().stream()
                    .mapToLong(each -> each.name().equals(field)
                            ? wholeNumber(each.value()) : totalOf(each.value(), field))
                    .sum();
            default -> 0;
        };
    }

    /** The whole number {@code value} writes. */
    private static long wholeNumber(Hir.Expr value) {
        return switch (value) {
            case Hir.IntLit number -> number.value();
            case Hir.Neg negated -> -wholeNumber(negated.operand());
            default -> throw new AssertionError("a whole number: " + value);
        };
    }

    /** The text {@code value} writes, under whatever names it wears. */
    private static String textOf(Hir.Expr value) {
        return switch (value) {
            case Hir.StringLit text -> text.value();
            case Hir.Apply applied when applied.args().size() == 1 ->
                    textOf(applied.args().getFirst());
            default -> throw new AssertionError("a text: " + value);
        };
    }

    /** Each model measured once for the class: the methods read the same models, and only read
     *  them. */
    private static final Map<String, Compilation> MEASURED = new ConcurrentHashMap<>();

    private static Compilation measured(String source) {
        return MEASURED.computeIfAbsent(source, text -> {
            Compilation compilation = Compilation.ofSource(text, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            return compilation;
        });
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
