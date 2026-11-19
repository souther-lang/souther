package souther.compiler.partition;

import souther.compiler.ACompiledModel;
import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.Proposition;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import org.junit.jupiter.api.Test;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A fold over a constant table that keeps the last row whose bound is met answers the step function
 * the table draws, so a comparison over what it answers is read at the bounds the table draws.
 *
 * <p>The step is one {@code if} in the source, applied once per row, so what is asserted is that
 * each application is read as its own. The same table written out as a chain of {@code if}s is the
 * reading to compare with. The walk is read so only where nothing it works out may end a run: the
 * seed and the rows are worked out before any application, whatever their value uses of what they
 * run.
 */
class AFoldOverAConstantTableIsTheStepFunctionItIsTest {

    private static final String ROW = "data Row = { grade: Int, lowerBound: Int }";

    private static final String HELD_ROW = ROW + "\n    invariant grade >= 0";

    private static final String ASCENDING = """
            [ Row { grade = 1, lowerBound = 100 }, Row { grade = 2, lowerBound = 200 },
              Row { grade = 3, lowerBound = 300 } ]""";

    /** A step that selects the grade of the last row whose bound the pay meets. */
    private static final String STEP = "(acc, r) -> if r.lowerBound <= pay then r.grade else acc";

    /** What the walk over the ascending table from a seed of nought states, measured once. */
    private static final class Literal {
        static final Proposition STATED =
                stated(compared("List.fold(%s, 0, %s)".formatted(STEP, ASCENDING)));
    }

    /**
     * What the fold states is what the same table written as a chain of {@code if}s states, under
     * an operation of the grade and another input: the same proposition, so that which grade a
     * bound selects is held and not only where the bounds fall.
     */
    @Test
    void theFoldStatesWhatTheChainOfIfsStates() {
        Proposition folded = stated("""
                let computed = List.fold((acc, r) -> if r.lowerBound <= pay then r else acc,
                    Row { grade = 0, lowerBound = 0 }, %s).grade
                if Int.abs(computed - cur) < 2 then 1 else 0""".formatted(ASCENDING));
        assertEquals(stated("""
                let computed = if pay >= 300 then 3 else if pay >= 200 then 2 else if pay >= 100 then 1 else 0
                if Int.abs(computed - cur) < 2 then 1 else 0"""), folded);
        assertFalse(Proposition.leavesSomethingUnread(folded));
    }

    /** The rows in the order they are written, one bound written twice: the last one met is the
     *  one kept. */
    @Test
    void theLastRowMetIsTheOneTheFoldStates() {
        assertEquals(stated("""
                        let computed = if pay >= 200 then 3 else if pay >= 100 then 2 else 0
                        if computed < 3 then 1 else 0"""),
                stated("""
                        let computed = List.fold(
                            (acc, r) -> if r.lowerBound <= pay then r else acc,
                            Row { grade = 0, lowerBound = 0 },
                            [ Row { grade = 1, lowerBound = 200 }, Row { grade = 2, lowerBound = 100 },
                              Row { grade = 3, lowerBound = 200 } ]).grade
                        if computed < 3 then 1 else 0"""));
    }

    /** A step that can end a run is not one whose earlier applications are dropped. */
    @Test
    void aStepThatMayEndARunIsNotReadAsAChoice() {
        Compilation compilation = ACompiledModel.measured("""
                module demo

                %s
                data Ok
                data No
                let table: List<Row> = %s
                behavior f : (pay: Int) -> Ok | No
                let f (pay) = {
                    let computed = List.fold(
                        (acc, r) -> if r.lowerBound / pay <= 1 then r.grade else acc, 0, table)
                    guard computed < 2 else No
                    Ok
                }
                """.formatted(ROW, ASCENDING), new Adequacy.Asked(Adequacy.Level.OFF, false));
        PartitionEvidence measured =
                compilation.db().ask(new Adequacy.Coverage("demo")).value().get("f");
        assertTrue(measured.notRead().stream().anyMatch(each -> each.reason()
                != UndividedPosition.Reason.EVALUATION_STOPS_NOT_FULLY_READ), measured::toString);
    }

    /**
     * A seed is worked out whole before any application, whatever of it its value uses: a
     * {@code let} whose value it does not use, a name bound to it, the fields of a construction an
     * access takes one of, and the condition of an {@code if} whose branches answer alike. Where
     * that may end a run the walk is not read as its last application, and where it cannot it is
     * read as it is with a seed written plain.
     */
    @Test
    void aSeedIsSkippedOverOnlyWhereWhatItRunsEndsNoRun() {
        String named = "let held = {\n    let spare = %s\n    0\n}\n"
                + compared("List.fold(%s, held, %s)".formatted(STEP, ASCENDING));
        assertEquals(Literal.STATED, stated(named.formatted("cur")));
        assertNotEquals(Literal.STATED, stated(named.formatted("Int.abs(cur)")));
        for (String seed : new String[] {"Row { grade = 0, lowerBound = Int.abs(cur) }.grade",
                "if Int.abs(cur) >= 0 then 0 else 0"}) {
            assertNotEquals(Literal.STATED, stated(compared(
                    "List.fold(%s, %s, %s)".formatted(STEP, seed, ASCENDING))), seed);
        }
    }

    /**
     * A row is worked out before any application, and so is its type's invariant: a row whose grade
     * may end a run is not skipped over, and neither is one whose invariant cannot be shown of the
     * input it is built of. The same row of an input under no invariant is read.
     */
    @Test
    void aRowThatMayEndARunIsNotSkippedOver() {
        String rows = "List.fold(%s, 0, [ Row { grade = %s, lowerBound = 100 },"
                + " Row { grade = 2, lowerBound = 200 } ])";
        assertTrue(Proposition.leavesSomethingUnread(
                stated(compared(rows.formatted(STEP, "Int.abs(cur)")))));
        String ofAnInput = compared(rows.formatted(STEP, "cur"));
        Proposition plain = stated(ofAnInput);
        assertFalse(Proposition.leavesSomethingUnread(plain));
        assertNotEquals(plain, stated(HELD_ROW, ofAnInput));
    }

    /**
     * A helper that hands its argument to a row, through a {@code let}, builds the row it was
     * handed: an invariant shown of that constant is held, and the walk reads as it does over rows
     * of a type that holds none.
     */
    @Test
    void anInvariantShownOfWhatAHelperHandsTheRowIsHeld() {
        String helpers = "\nlet rowOf (g: Int): Row = Row { grade = g, lowerBound = 100 }"
                + "\nlet through (n: Int): Row = {\n    let k = n\n    rowOf(k)\n}";
        String walked = compared("List.fold(%s, 0, [ through(1), rowOf(2) ])".formatted(STEP));
        assertEquals(stated(ROW + helpers, walked), stated(HELD_ROW + helpers, walked));
    }

    /**
     * A table of constants is read as the rows it holds where the value that writes it was built
     * by the code that ships without breaking its invariant, which is about the whole list and is
     * not worked out here. Reading no input is not that: the same table built out of an input is
     * built on each run, and is not taken so.
     */
    @Test
    void aTableIsReadAsItsRowsOnceTheValueThatWritesItIsBuilt() {
        String declarations = """
                %s
                data Table = List<Row>
                    invariant threeRows = List.length(value) == 3
                    invariant distinctGrades = List.allDistinctBy(.grade, value)
                let rowOf (g: Int, lo: Int): Row = Row { grade = g, lowerBound = lo }
                """.formatted(ROW);
        String folded = compared("List.fold(%s, 0, table.value)".formatted(STEP));
        assertEquals(Literal.STATED, stated(declarations
                + "let table = Table([ rowOf(1, 100), rowOf(2, 200), rowOf(3, 300) ])\n", folded));
        assertNotEquals(Literal.STATED, stated(declarations,
                "let table = Table([ rowOf(cur, 100), rowOf(2, 200), rowOf(3, 300) ])\n"
                        + folded));
    }

    /** A table an input decides is no step function written down. */
    @Test
    void aTableTheInputDecidesIsNotAStepFunction() {
        Compilation compilation = ACompiledModel.measured("""
                module demo

                %s
                data Ok
                data No
                behavior f : (pay: Int, rows: List<Row>) -> Ok | No
                let f (pay, rows) = {
                    let computed = List.fold((acc, r) -> if r.lowerBound <= pay then r else acc,
                        Row { grade = 0, lowerBound = 0 }, rows).grade
                    guard computed < 2 else No
                    Ok
                }
                """.formatted(ROW), new Adequacy.Asked(Adequacy.Level.OFF, false));
        PartitionEvidence measured =
                compilation.db().ask(new Adequacy.Coverage("demo")).value().get("f");
        assertTrue(measured.notRead().stream().anyMatch(each -> each.reason()
                != UndividedPosition.Reason.EVALUATION_STOPS_NOT_FULLY_READ), measured::toString);
    }

    /**
     * What a construction an {@code if} tests for is refused by is the branch the {@code if}
     * takes, so a seed that is such an {@code if} ends no run on a refusal.
     */
    @Test
    void aRefusalOfAConstructionAnIfTestsForEndsNoRun() {
        assertEquals(Literal.STATED, stated(HELD_ROW, compared(
                "List.fold(%s, if Row { grade = cur, lowerBound = 100 } as row then 0 else 0, %s)"
                        .formatted(STEP, ASCENDING))));
    }

    private static String compared(String computed) {
        return "let computed = %s\nif computed < 2 then 1 else 0".formatted(computed);
    }

    /** What the condition of the one fork that ends a body written {@code body} states. */
    private static Proposition stated(String body) {
        return stated(ROW, body);
    }

    /** The same, over the declarations {@code declarations}. */
    private static Proposition stated(String declarations, String body) {
        Compilation compilation = ACompiledModel.answered("""
                module demo

                %s

                behavior f : (cur: Int, pay: Int) -> Int
                let f (cur, pay) = {
                %s
                }
                """.formatted(declarations, body.indent(4).stripTrailing()));
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        AnalysisBody analysis = checked.analysisBodies().get("f");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("f");
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        Core e = Core.withoutStanding(analysis.core());
        while (e instanceof Core.LetIn let) {
            reads = reads.and(let.binder(), let.value());
            e = Core.withoutStanding(let.body());
        }
        Core.If fork = assertInstanceOf(Core.If.class, e, "the body ends in one fork");
        return Pullback.ofATruth(fork.cond(), reads, inputs.reading(rules), Optional.empty())
                .proposition();
    }
}
