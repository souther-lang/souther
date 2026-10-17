package souther.compiler.examples;

import souther.compiler.generated.EvaluationArtifact;
import souther.compiler.generated.MemoryClassLoader;
import souther.compiler.observe.ArmObservation;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.RowIdentity;
import souther.compiler.observe.Verdict;
import souther.compiler.program.CheckedAssertion;
import souther.compiler.program.CheckedHelper;
import souther.compiler.program.CheckedProgram;
import souther.compiler.program.CheckedRow;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;
import souther.runtime.Values;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An output holding a row where its answer is, by the language's equality over the value the row's
 * assertion computes, decides what {@link CheckedRow.SelfContained#holds} decides over the answer
 * brought back.
 *
 * <p>The two are different code. One compares an observation of the answer with what the row was read
 * as stating; the other is the run-time equality a host's own runtime implements — on the JVM,
 * {@link Values#equal} — over the stated value built where the answer is. Where they part, a row holds
 * where the answer comes back and not where it stays, or the other way round, and nothing about the
 * row says which.
 *
 * <p>Both values are the module's own: the stated one is what the assertion's definition answers, and
 * the answer is a value the same program builds, handed to a behavior as a row's input. So each pair
 * is two values a program can produce at one type, and the observation held against the row is the
 * one this compiler made of the answer when it ran that row.
 */
class AStatedValueIsKeptByTheLanguagesEqualityWhereverTheAnswerIsTest {

    /** A value a row states at {@code type}, and an answer of that type. */
    private record Pair(String says, String type, String stated, String answered) {}

    private static final List<Pair> PAIRS = List.of(
            new Pair("an amount and the same amount at another scale", "Decimal", "1.0m", "1.00m"),
            new Pair("an amount and another", "Decimal", "1.0m", "1.1m"),
            new Pair("a set and the same elements met in another order", "Set<Int>",
                    "Set.fromList([1, 2])", "Set.fromList([2, 1])"),
            new Pair("a set and one holding something else", "Set<Int>",
                    "Set.fromList([1, 2])", "Set.fromList([1, 3])"),
            new Pair("a map and the same entries in another order", "Map<String, Int>",
                    "Map.fromList([(\"a\", 1), (\"b\", 2)])",
                    "Map.fromList([(\"b\", 2), (\"a\", 1)])"),
            new Pair("a map answering differently under a key", "Map<String, Int>",
                    "Map.fromList([(\"a\", 1)])", "Map.fromList([(\"a\", 2)])"),
            new Pair("a list and the same list", "List<Int>", "[1, 2]", "[1, 2]"),
            new Pair("a list and the same elements in another order", "List<Int>",
                    "[1, 2]", "[2, 1]"),
            new Pair("a list of lists and the same", "List<List<Int>>", "[[1], []]", "[[1], []]"),
            new Pair("a list of lists differing inside one of them", "List<List<Int>>",
                    "[[1], []]", "[[1], [2]]"),
            new Pair("an empty list of lists and another", "List<List<Int>>", "[]", "[]"),
            new Pair("an empty list built as one of sets, and an empty list of lists",
                    "List<List<Int>>", "List.take(0, [Set.fromList([1])])", "[]"),
            new Pair("a list of sets met in another order", "List<Set<Int>>",
                    "[Set.fromList([1, 2])]", "[Set.fromList([2, 1])]"),
            new Pair("an optional field holding a value and the same", "Slot",
                    "Slot { held = 1 }", "Slot { held = 1 }"),
            new Pair("an optional field holding nothing and the same", "Slot", "Slot { }",
                    "Slot { }"),
            new Pair("an optional field holding nothing and one holding a value", "Slot",
                    "Slot { }", "Slot { held = 1 }"),
            new Pair("one case of a sum and the same", "Weight", "Kg { n = 1 }", "Kg { n = 1 }"),
            new Pair("two cases of a sum holding the same", "Weight", "Kg { n = 1 }",
                    "Lb { n = 1 }"),
            new Pair("one case and the same case holding something else", "Weight",
                    "Kg { n = 1 }", "Kg { n = 2 }"),
            new Pair("a newtype and the same", "Box", "Box { at = AmountN(1) }",
                    "Box { at = AmountN(1) }"),
            new Pair("a newtype and another", "Box", "Box { at = AmountN(1) }",
                    "Box { at = AmountN(2) }"));

    private static final String DECLARATIONS = """
            module demo

            data Slot = { held: Int? }
            data Kg = { n: Int }
            data Lb = { n: Int }
            data Weight = Kg | Lb
            data AmountN = Int
            data Box = { at: AmountN }
            """;

    /** The module: for each pair, a behavior answering at its type with a row stating one value,
     *  and a behavior taking that type with a row handing it the other. */
    private static String module() {
        StringBuilder out = new StringBuilder(DECLARATIONS);
        for (int i = 0; i < PAIRS.size(); i++) {
            Pair pair = PAIRS.get(i);
            out.append("""

                    behavior answers%1$d : (n: Int) -> %2$s

                    behavior takes%1$d : (x: %2$s) -> Int

                    example answers%1$d
                        | "stated" : (1) -> %3$s

                    example takes%1$d
                        | "answered" : (%4$s) -> <?>
                    """.formatted(i, pair.type(), pair.stated(), pair.answered()));
        }
        return out.toString();
    }

    private static CheckedRow.Statement statementOf(CheckedProgram program, String behavior,
                                                    String named) {
        return program.module("demo").behavior(new ValueName.Behavior("demo", behavior)).rows()
                .stream()
                .filter(it -> it.identity().equals(new RowIdentity.Named(named)))
                .findFirst()
                .orElseThrow(() -> new AssertionError("no row `" + named + "` of " + behavior))
                .statement();
    }

    private static Object ran(OperandRunner operands, CheckedHelper helper) {
        return operands.run(assertInstanceOf(ValueName.Helper.class, helper.declares()).name());
    }

    /** What each pair comes to on the two sides, and which pairs they part on. */
    private record Decided(List<String> equal, List<String> differ, List<String> parted) {}

    private static Decided decided;

    /** Decided once for the class: both laws read the same pairs, and deciding them compiles the
     *  module twice. */
    private static synchronized Decided decided() {
        if (decided == null) {
            decided = decide();
        }
        return decided;
    }

    private static Decided decide() {
        String source = module();
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        EvaluationArtifact runs =
                compilation.db().ask(new Output.Evaluated("demo", ArmObservation.OMIT)).value();
        OperandRunner operands = new OperandRunner("demo",
                new MemoryClassLoader(runs.classes(),
                        AStatedValueIsKeptByTheLanguagesEqualityWhereverTheAnswerIsTest.class
                                .getClassLoader()));
        CheckedProgram program = CheckedProgram.of(List.of(source));

        List<String> equal = new ArrayList<>();
        List<String> differ = new ArrayList<>();
        List<String> parted = new ArrayList<>();
        for (int i = 0; i < PAIRS.size(); i++) {
            Pair pair = PAIRS.get(i);
            CheckedRow.SelfContained stated = assertInstanceOf(CheckedRow.SelfContained.class,
                    statementOf(program, "answers" + i, "stated"));
            CheckedRow.AnswerOwed given = assertInstanceOf(CheckedRow.AnswerOwed.class,
                    statementOf(program, "takes" + i, "answered"));
            CheckedHelper computing = assertInstanceOf(CheckedAssertion.Value.class,
                    stated.assertion()).computing();

            ObservedValue answered = given.states().inputs().getFirst();
            assertNull(answered.unread(), () -> pair.says() + ": the answer was read in full");
            boolean held = stated.holds(answered) instanceof Verdict.Held;
            boolean same = Values.equal(ran(operands, computing),
                    ran(operands, given.inputDefinitions().getFirst()));

            (same ? equal : differ).add(pair.says());
            if (held != same) {
                parted.add(pair.says() + " (held " + held + ", equal " + same + ")");
            }
        }
        return new Decided(equal, differ, parted);
    }

    @Test
    void whatTheLanguagesEqualityDecidesIsWhatHoldsDecides() {
        assertEquals(List.of(), decided().parted());
    }

    /**
     * And the pairs say both things. A law over pairs that were all the same value, or all not, is
     * one a comparison answering the same to everything would keep.
     */
    @Test
    void andThePairsAreBothTheSameValueAndNot() {
        Decided decided = decided();

        assertTrue(decided.equal().size() >= 8, () -> "pairs of one value: " + decided.equal());
        assertTrue(decided.differ().size() >= 8, () -> "pairs of two: " + decided.differ());
    }

    /**
     * A row stating a case is held by the case the answer is, whatever stands under it — which is
     * what an output holding {@link CheckedAssertion.Case} decides.
     */
    @Test
    void aStatedCaseIsHeldByTheCaseTheAnswerIs() {
        String source = DECLARATIONS + """

                behavior weighs : (n: Int) -> Weight

                behavior takes : (x: Weight) -> Int

                example weighs
                    | "a kg" : (1) -> Kg

                example takes
                    | "one kg" : (Kg { n = 1 }) -> <?>
                    | "two kg" : (Kg { n = 2 }) -> <?>
                    | "one lb" : (Lb { n = 1 }) -> <?>
                """;
        CheckedProgram program = CheckedProgram.of(List.of(source));
        CheckedRow.SelfContained stated = assertInstanceOf(CheckedRow.SelfContained.class,
                statementOf(program, "weighs", "a kg"));
        TypeSymbol expected = assertInstanceOf(CheckedAssertion.Case.class, stated.assertion())
                .expected();

        List<String> parted = new ArrayList<>();
        int held = 0;
        for (String answer : List.of("one kg", "two kg", "one lb")) {
            ObservedValue answered = assertInstanceOf(CheckedRow.AnswerOwed.class,
                    statementOf(program, "takes", answer)).states().inputs().getFirst();
            boolean holds = stated.holds(answered) instanceof Verdict.Held;
            boolean isTheCase = expected.equals(answered.declaredAs());
            held += holds ? 1 : 0;
            if (holds != isTheCase) {
                parted.add(answer);
            }
        }

        assertEquals(List.of(), parted);
        assertEquals(2, held, "the two kgs hold and the lb does not");
    }
}
