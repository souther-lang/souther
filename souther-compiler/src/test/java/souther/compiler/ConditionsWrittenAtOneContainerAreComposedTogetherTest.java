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
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Conditions on the way to a rule that are written at one container are composed as one demand on
 * it, whichever order the body states them in.
 *
 * <p>A total of the elements, what every element is to meet, how many the container holds and how
 * many of its elements meet something are each a demand on the one container a row writes. Placed
 * one after another, the first took the container and the others were the conditions the row was
 * composed without; so the order a body happened to state them in decided which rules got a row.
 *
 * <p>Held by running the rows: each row composed for a rule is put back as an example, answered
 * with what the body works out over the numbers the row holds — read here, apart from anything the
 * compiler read — so a row that stands short of its rule is an example the model answers
 * otherwise. And which rules are composed a row is held too, so a rule going without one is a
 * change this says.
 */
class ConditionsWrittenAtOneContainerAreComposedTogetherTest {

    /** A total, and then that every element is at least five: three elements of five meet both. */
    private static final String A_TOTAL_THEN_EVERY_ELEMENT = """
            module p
            data Line = { q: Int }
            data Lines = List<Line>
                invariant several = List.length(value) >= 3
            behavior pick : (ls: Lines, n: Int) -> Int
            let pick (ls, n) = {
                guard List.sum(List.map(l -> l.q, ls.value)) >= 10 else 0
                guard List.all(l -> l.q >= 5, ls.value) else 1
                if n > 3 then 2 else 3
            }
            """;

    /** The same two the other way round. Below the total is a total no list of three elements of
     *  five or more comes to, which is the one rule no row reaches. */
    private static final String EVERY_ELEMENT_THEN_A_TOTAL = """
            module p
            data Line = { q: Int }
            data Lines = List<Line>
                invariant several = List.length(value) >= 3
            behavior pick : (ls: Lines, n: Int) -> Int
            let pick (ls, n) = {
                guard List.all(l -> l.q >= 5, ls.value) else 1
                guard List.sum(List.map(l -> l.q, ls.value)) >= 10 else 0
                if n > 3 then 2 else 3
            }
            """;

    /** That every element is at least five, of elements the rules keep at two at the most: only a
     *  list holding none meets it, and the list holding none is composed. */
    private static final String EVERY_ELEMENT_OF_NONE = """
            module p
            data Line = { q: Int }
                invariant small = q >= 0 && q <= 2
            behavior pick : (ls: List<Line>, n: Int) -> Int
            let pick (ls, n) = {
                guard List.sum(List.map(l -> l.q, ls)) <= 3 else 0
                guard List.all(l -> l.q >= 5, ls) else 1
                if n > 3 then 2 else 3
            }
            """;

    /** A total added to another parameter, that parameter held low, and the list held to three: one
     *  statement over two locations joins what is written at both. */
    private static final String A_TOTAL_BESIDE_ANOTHER_NUMBER = """
            module p
            data Line = { q: Int }
                invariant minimum = q >= 3
            behavior pick : (ls: List<Line>, y: Int, n: Int) -> Int
            let pick (ls, y, n) = {
                guard List.sum(List.map(l -> l.q, ls)) + y >= 10 else 0
                guard y <= 3 else 1
                guard List.length(ls) >= 3 else 2
                if n > 3 then 3 else 4
            }
            """;

    /** How many the list holds, and then what its elements add up to: the elements are at most
     *  five, so a list of one does not come to eight. */
    private static final String HOW_MANY_THEN_A_TOTAL = """
            module p
            data Line = { a: Int }
                invariant small = a >= 0 && a <= 5
            behavior pick : (ls: List<Line>, n: Int) -> Int
            let pick (ls, n) = {
                guard List.length(ls) >= 1 else 0
                guard List.sum(List.map(l -> l.a, ls)) >= 8 else 1
                if n > 3 then 2 else 3
            }
            """;

    /**
     * A total and how many elements meet something, which nothing here composes one list for. The
     * count decides which elements the list holds, so it is composed and the total is read off it
     * where the row runs; the rule where the elements meeting it are too few for the total is the
     * one no row is composed for, and it is said as the pair nothing composes one value for.
     */
    private static final String A_TOTAL_AND_HOW_MANY_MEET = """
            module p
            data Line = { q: Int }
            behavior pick : (ls: List<Line>, n: Int) -> Int
            let pick (ls, n) = {
                guard List.sum(List.map(l -> l.q, ls)) >= 10 else 0
                guard List.length(List.filter(l -> l.q >= 5, ls)) >= 3 else 1
                if n > 3 then 2 else 3
            }
            """;

    /** That every element is at least five, and then that some element is: a list of one element
     *  of five meets both, and the list holding none meets the first alone. */
    private static final String EVERY_ELEMENT_THEN_HOW_MANY_MEET = """
            module p
            data Line = { q: Int }
            behavior pick : (ls: List<Line>, n: Int) -> Int
            let pick (ls, n) = {
                guard List.all(l -> l.q >= 5, ls) else 0
                guard List.length(List.filter(l -> l.q >= 5, ls)) >= 1 else 1
                if n > 3 then 2 else 3
            }
            """;

    /** The same two the other way round. */
    private static final String HOW_MANY_MEET_THEN_EVERY_ELEMENT = """
            module p
            data Line = { q: Int }
            behavior pick : (ls: List<Line>, n: Int) -> Int
            let pick (ls, n) = {
                guard List.length(List.filter(l -> l.q >= 5, ls)) >= 1 else 1
                guard List.all(l -> l.q >= 5, ls) else 0
                if n > 3 then 2 else 3
            }
            """;

    /** That every element is at least five as one part of a condition, which is no statement a
     *  count is of, beside how many meet it. */
    private static final String EVERY_ELEMENT_AS_A_PART = """
            module p
            data Line = { q: Int }
            behavior pick : (ls: List<Line>, m: Int, n: Int) -> Int
            let pick (ls, m, n) = {
                guard List.all(l -> l.q >= 5, ls) && m >= 0 else 0
                guard List.length(List.filter(l -> l.q >= 5, ls)) >= 1 else 1
                if n > 3 then 2 else 3
            }
            """;

    /** That every element is at least ten, and that some element is five at the most: no list
     *  meets both, so the rules past them are composed no row — and the list holding none meets
     *  the first and not the second. */
    private static final String EVERY_ELEMENT_AGAINST_HOW_MANY_MEET = """
            module p
            data Line = { q: Int }
            behavior pick : (ls: List<Line>, n: Int) -> Int
            let pick (ls, n) = {
                guard List.all(l -> l.q >= 10, ls) else 0
                guard List.length(List.filter(l -> l.q <= 5, ls)) >= 1 else 1
                if n > 3 then 2 else 3
            }
            """;

    /** The same two the other way round. */
    private static final String HOW_MANY_MEET_AGAINST_EVERY_ELEMENT = """
            module p
            data Line = { q: Int }
            behavior pick : (ls: List<Line>, n: Int) -> Int
            let pick (ls, n) = {
                guard List.length(List.filter(l -> l.q <= 5, ls)) >= 1 else 1
                guard List.all(l -> l.q >= 10, ls) else 0
                if n > 3 then 2 else 3
            }
            """;

    /** The same two with every element's as one part of a condition. */
    private static final String HOW_MANY_MEET_AGAINST_EVERY_ELEMENT_AS_A_PART = """
            module p
            data Line = { q: Int }
            behavior pick : (ls: List<Line>, m: Int, n: Int) -> Int
            let pick (ls, m, n) = {
                guard List.all(l -> l.q >= 10, ls) && m >= 0 else 0
                guard List.length(List.filter(l -> l.q <= 5, ls)) >= 1 else 1
                if n > 3 then 2 else 3
            }
            """;

    /** That every element is at least five, and that some element is at least seven: both hold of
     *  a list, and an element meeting the second is not every element meeting the first. */
    private static final String EVERY_ELEMENT_AND_A_STRICTER_COUNT = """
            module p
            data Line = { q: Int }
            behavior pick : (ls: List<Line>, n: Int) -> Int
            let pick (ls, n) = {
                guard List.all(l -> l.q >= 5, ls) else 0
                guard List.length(List.filter(l -> l.q >= 7, ls)) >= 1 else 1
                if n > 3 then 2 else 3
            }
            """;

    /** The same two the other way round. */
    private static final String A_STRICTER_COUNT_AND_EVERY_ELEMENT = """
            module p
            data Line = { q: Int }
            behavior pick : (ls: List<Line>, n: Int) -> Int
            let pick (ls, n) = {
                guard List.length(List.filter(l -> l.q >= 7, ls)) >= 1 else 1
                guard List.all(l -> l.q >= 5, ls) else 0
                if n > 3 then 2 else 3
            }
            """;

    /** The same two with every element's as one part of a condition. */
    private static final String EVERY_ELEMENT_AS_A_PART_AND_A_STRICTER_COUNT = """
            module p
            data Line = { q: Int }
            behavior pick : (ls: List<Line>, m: Int, n: Int) -> Int
            let pick (ls, m, n) = {
                guard List.all(l -> l.q >= 5, ls) && m >= 0 else 0
                guard List.length(List.filter(l -> l.q >= 7, ls)) >= 1 else 1
                if n > 3 then 2 else 3
            }
            """;

    /** Each model, with what its body answers over the inputs a row holds and the answers of the
     *  rules some row of it is composed for. */
    private static final Map<String, Answered> ANSWERED = Map.ofEntries(
            Map.entry(A_TOTAL_THEN_EVERY_ELEMENT, new Answered(row ->
                    total(row.get(0), "q") < 10 ? 0
                            : !every(row.get(0), "q", 5) ? 1 : number(row.get(1)) > 3 ? 2 : 3,
                    Set.of(0, 1, 2, 3))),
            Map.entry(EVERY_ELEMENT_THEN_A_TOTAL, new Answered(row ->
                    !every(row.get(0), "q", 5) ? 1
                            : total(row.get(0), "q") < 10 ? 0 : number(row.get(1)) > 3 ? 2 : 3,
                    Set.of(1, 2, 3))),
            Map.entry(EVERY_ELEMENT_OF_NONE, new Answered(row ->
                    total(row.get(0), "q") > 3 ? 0
                            : !every(row.get(0), "q", 5) ? 1 : number(row.get(1)) > 3 ? 2 : 3,
                    Set.of(0, 1, 2, 3))),
            Map.entry(A_TOTAL_BESIDE_ANOTHER_NUMBER, new Answered(row ->
                    total(row.get(0), "q") + number(row.get(1)) < 10 ? 0
                            : number(row.get(1)) > 3 ? 1
                            : elementsOf(row.get(0)).size() < 3 ? 2
                            : number(row.get(2)) > 3 ? 3 : 4,
                    Set.of(0, 1, 2, 3, 4))),
            Map.entry(HOW_MANY_THEN_A_TOTAL, new Answered(row ->
                    elementsOf(row.get(0)).isEmpty() ? 0
                            : total(row.get(0), "a") < 8 ? 1 : number(row.get(1)) > 3 ? 2 : 3,
                    Set.of(0, 1, 2, 3))),
            Map.entry(A_TOTAL_AND_HOW_MANY_MEET, new Answered(row ->
                    total(row.get(0), "q") < 10 ? 0
                            : meeting(row.get(0), "q", 5) < 3 ? 1
                            : number(row.get(1)) > 3 ? 2 : 3,
                    Set.of(0, 2, 3))),
            Map.entry(EVERY_ELEMENT_THEN_HOW_MANY_MEET, new Answered(row ->
                    !every(row.get(0), "q", 5) ? 0
                            : meeting(row.get(0), "q", 5) < 1 ? 1
                            : number(row.get(1)) > 3 ? 2 : 3,
                    Set.of(0, 1, 2, 3))),
            Map.entry(HOW_MANY_MEET_THEN_EVERY_ELEMENT, new Answered(row ->
                    meeting(row.get(0), "q", 5) < 1 ? 1
                            : !every(row.get(0), "q", 5) ? 0
                            : number(row.get(1)) > 3 ? 2 : 3,
                    Set.of(0, 1, 2, 3))),
            Map.entry(EVERY_ELEMENT_AS_A_PART, new Answered(row ->
                    !every(row.get(0), "q", 5) || number(row.get(1)) < 0 ? 0
                            : meeting(row.get(0), "q", 5) < 1 ? 1
                            : number(row.get(2)) > 3 ? 2 : 3,
                    Set.of(0, 1, 2, 3))),
            Map.entry(EVERY_ELEMENT_AGAINST_HOW_MANY_MEET, new Answered(row ->
                    !every(row.get(0), "q", 10) ? 0
                            : atMost(row.get(0), "q", 5) < 1 ? 1
                            : number(row.get(1)) > 3 ? 2 : 3,
                    Set.of(0, 1))),
            Map.entry(HOW_MANY_MEET_AGAINST_EVERY_ELEMENT, new Answered(row ->
                    atMost(row.get(0), "q", 5) < 1 ? 1
                            : !every(row.get(0), "q", 10) ? 0
                            : number(row.get(1)) > 3 ? 2 : 3,
                    Set.of(0, 1))),
            Map.entry(HOW_MANY_MEET_AGAINST_EVERY_ELEMENT_AS_A_PART, new Answered(row ->
                    !every(row.get(0), "q", 10) || number(row.get(1)) < 0 ? 0
                            : atMost(row.get(0), "q", 5) < 1 ? 1
                            : number(row.get(2)) > 3 ? 2 : 3,
                    Set.of(0, 1))),
            Map.entry(EVERY_ELEMENT_AND_A_STRICTER_COUNT, new Answered(row ->
                    !every(row.get(0), "q", 5) ? 0
                            : meeting(row.get(0), "q", 7) < 1 ? 1
                            : number(row.get(1)) > 3 ? 2 : 3,
                    Set.of(0, 1, 2, 3))),
            Map.entry(A_STRICTER_COUNT_AND_EVERY_ELEMENT, new Answered(row ->
                    meeting(row.get(0), "q", 7) < 1 ? 1
                            : !every(row.get(0), "q", 5) ? 0
                            : number(row.get(1)) > 3 ? 2 : 3,
                    Set.of(0, 1, 2, 3))),
            Map.entry(EVERY_ELEMENT_AS_A_PART_AND_A_STRICTER_COUNT, new Answered(row ->
                    !every(row.get(0), "q", 5) || number(row.get(1)) < 0 ? 0
                            : meeting(row.get(0), "q", 7) < 1 ? 1
                            : number(row.get(2)) > 3 ? 2 : 3,
                    Set.of(0, 1, 2, 3))));

    /** What a model's body works out to over a row's inputs, and the answers of the rules a row is
     *  composed for. */
    private record Answered(Function<List<Hir.Expr>, Integer> by, Set<Integer> composedFor) {}

    @Test
    void everyRuleIsComposedARowThatTakesItWhicheverOrderTheConditionsAreIn() {
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
                    () -> "a row for the rules this model has one for: " + examples + "\n" + model);

            // Run and not measured: an example whose answer is not the program's is an error,
            // which is all this asks of the rows.
            Compilation answeredBy = Compilation.ofSource(model + "example pick\n"
                    + String.join("\n", examples) + "\n", "Main");
            answeredBy.answerEverything();
            assertEquals(List.of(), answeredBy.errors().stream()
                    .map(each -> each.diagnostic().code() + " " + each.diagnostic().said())
                    .toList(), () -> "each row is answered as its inputs say: " + examples);
        });
    }

    /**
     * The rule nothing is composed for is said as the pair of numbers no one list is composed for,
     * and as nothing about the model.
     */
    @Test
    void aTotalAndACountNothingComposesOneListForAreSaidAsThat() {
        String report = report(measured(A_TOTAL_AND_HOW_MANY_MEET));
        List<String> lines = report.lines().toList();
        List<Integer> opened = new ArrayList<>();
        for (int i = 0; i < lines.size(); i++) {
            if (lines.get(i).contains("nothing could show a row can be written at")
                    && lines.get(i).contains("decision rule")) {
                opened.add(i);
            }
        }

        assertEquals(1, opened.size(), () -> report);
        List<String> under = lines.subList(opened.getFirst() + 1, lines.size()).stream()
                .takeWhile(line -> line.startsWith("          · ")).toList();
        assertTrue(under.stream().anyMatch(line -> line.contains("a condition on another number"
                + " taken where this row is already being written for one")), () -> report);
    }

    /**
     * A count the way leaves several of is composed beside a condition's numbers at the least of
     * them, which is a count this chose: that nothing composes at it says nothing of the counts
     * above it, and no point past it is said to be one the rules leave no value at.
     *
     * <p>Every element at least five and at most three of them, so how many meet "at least five"
     * is how many there are: none of them is no list holding one, and one of them is.
     */
    @Test
    void theLeastOfACountsLeftIsNoProofTheRulesLeaveNothing() {
        String report = report(measured("""
                module p
                data Line = { q: Int }
                    invariant big = q >= 5
                data Lines = List<Line>
                    invariant few = List.length(value) <= 3
                behavior pick : (ls: Lines, n: Int) -> Int
                let pick (ls, n) = {
                    guard List.length(List.filter(l -> l.q >= 5, ls.value)) <= 3 else 0
                    guard List.length(ls.value) >= 1 else 1
                    if n > 3 then 2 else 3
                }
                """));
        List<String> past = report.lines()
                .filter(line -> line.contains("read as pick/n:")
                        || line.contains("decision rule"))
                .toList();

        assertTrue(!past.isEmpty(), () -> report);
        for (String line : past) {
            assertTrue(!line.contains("no value can"),
                    () -> "nothing past the count is said to be what the rules leave: " + line);
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

    /** The elements of the list {@code value} writes, under whatever names it wears. */
    private static List<Hir.Expr> elementsOf(Hir.Expr value) {
        return switch (value) {
            case Hir.ListLit list -> list.elements();
            case Hir.Apply applied when applied.args().size() == 1 ->
                    elementsOf(applied.args().getFirst());
            default -> throw new AssertionError("a list: " + value);
        };
    }

    /** The whole number each element of {@code list} holds at {@code field}. */
    private static List<Long> fieldOf(Hir.Expr list, String field) {
        List<Long> out = new ArrayList<>();
        for (Hir.Expr element : elementsOf(list)) {
            Hir.NewData record = (Hir.NewData) element;
            out.add(number(record.inits().stream().filter(each -> each.name().equals(field))
                    .findFirst().orElseThrow().value()));
        }
        return out;
    }

    private static long total(Hir.Expr list, String field) {
        return fieldOf(list, field).stream().mapToLong(Long::longValue).sum();
    }

    private static boolean every(Hir.Expr list, String field, long least) {
        return fieldOf(list, field).stream().allMatch(each -> each >= least);
    }

    private static long meeting(Hir.Expr list, String field, long least) {
        return fieldOf(list, field).stream().filter(each -> each >= least).count();
    }

    private static long atMost(Hir.Expr list, String field, long most) {
        return fieldOf(list, field).stream().filter(each -> each <= most).count();
    }

    /** The whole number {@code value} writes. */
    private static long number(Hir.Expr value) {
        return switch (value) {
            case Hir.IntLit number -> number.value();
            case Hir.Neg negated -> -number(negated.operand());
            default -> throw new AssertionError("a whole number: " + value);
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
