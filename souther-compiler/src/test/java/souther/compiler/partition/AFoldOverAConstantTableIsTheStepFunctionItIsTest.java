package souther.compiler.partition;

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
import souther.compiler.query.Measurement;
import souther.compiler.query.PartitionEvidence;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

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
 * reading to compare with: the classes of the input are the ones that chain draws.
 */
class AFoldOverAConstantTableIsTheStepFunctionItIsTest {

    private static final String ASCENDING = """
            [ Row { grade = 1, lowerBound = 100 }, Row { grade = 2, lowerBound = 200 },
              Row { grade = 3, lowerBound = 300 } ]""";

    private static final String BY_HAND = """
            if pay >= 300 then 3 else if pay >= 200 then 2 else if pay >= 100 then 1 else 0""";

    @Test
    void whateverIsDoneWithTheGradeIsReadAtEveryBoundOfTheTable() {
        for (String condition : List.of("computed < 2", "computed - cur < 2",
                "Int.abs(computed - cur) < 2")) {
            PartitionEvidence folded = measured(ASCENDING, "r.lowerBound <= monthly", condition);
            assertEquals(List.of(), notRead(folded), condition);
            assertEquals(classesOf(measuredByHand(BY_HAND, condition), "pay"),
                    classesOf(folded, "pay"), condition);
        }
    }

    /** Bounds written out of order, and one written twice, are the bounds of the table all the same. */
    @Test
    void boundsWrittenOutOfOrderAreReadAtEachOfThem() {
        PartitionEvidence measured = measured("""
                [ Row { grade = 1, lowerBound = 200 }, Row { grade = 2, lowerBound = 100 },
                  Row { grade = 3, lowerBound = 200 } ]""", "r.lowerBound <= monthly",
                "computed < 3");
        assertEquals(List.of(), notRead(measured));
        assertEquals(List.of("pay/x < 100", "pay/100 <= x < 200", "pay/200 <= x"),
                classesOf(measured, "pay"));
    }

    /** A walk over no row ends with its seed, and over one row it draws that row's bound. */
    @Test
    void aTableOfNoRowIsItsSeedAndOfOneRowIsOneBound() {
        PartitionEvidence none = measured("[]", "r.lowerBound <= monthly", "computed < 2");
        assertEquals(List.of(), notRead(none));
        PartitionEvidence one = measured("[ Row { grade = 1, lowerBound = 100 } ]",
                "r.lowerBound <= monthly", "computed < 1");
        assertEquals(List.of(), notRead(one));
        assertEquals(List.of("pay/x < 100", "pay/100 <= x"), classesOf(one, "pay"));
    }

    /** What the step selects may be a number as well as a row. */
    @Test
    void aWalkThatSelectsANumberIsReadAsOneThatSelectsARow() {
        PartitionEvidence measured = measure(Compilation.ofSource("""
                module demo

                data Row = { grade: Int, lowerBound: Int }
                data Ok
                data No
                let table: List<Row> = %s
                behavior f : (pay: Int) -> Ok | No
                let f (pay) = {
                    let computed = List.fold((acc, r) -> if r.lowerBound <= pay then r.grade else acc,
                        0, table)
                    guard computed < 2 else No
                    Ok
                }
                """.formatted(ASCENDING), "Main"), "f");
        assertEquals(List.of(), notRead(measured));
        assertEquals(List.of("pay/x < 100", "pay/100 <= x < 200", "pay/200 <= x < 300",
                "pay/300 <= x"), classesOf(measured, "pay"));
    }

    /** A step that can end a run for any reason is not one whose earlier applications are dropped. */
    @Test
    void aStepThatMayEndARunIsNotReadAsAChoice() {
        for (String selects : List.of("r.lowerBound / monthly <= 1",
                "r.lowerBound + monthly >= 0", "r.lowerBound * monthly >= 0")) {
            assertFalse(notRead(measured(ASCENDING, selects, "computed < 2")).isEmpty(), selects);
        }
    }

    /**
     * The seed and the rows are worked out before any application, so a walk whose seed or rows a
     * run can end on is not the answer of its last application. What a run is ended by is the
     * owners' to say ({@code WhatARunMayEndFor}, and the declaration's invariant for a
     * construction): an input at the least {@code Int} ends the run in {@code Int.abs}, and a row
     * of a type with an invariant may be refused. The same walks with a seed and rows that end
     * none are read, so it is those and not the walk that leave the comparison unread.
     */
    @Test
    void aSeedOrARowThatMayEndARunIsNotSkippedOver() {
        String plain = "data Row = { grade: Int, lowerBound: Int }";
        String held = plain + "\n    invariant grade >= 0";
        String step = "(acc, r) -> if r.lowerBound <= pay then r.grade else acc";
        String rows = "[ Row { grade = %s, lowerBound = 100 }, Row { grade = 2, lowerBound = 200 } ]";
        for (String walked : List.of(
                "List.fold(%s, Int.abs(cur), %s)".formatted(step, ASCENDING),
                "List.fold(%s, 0, %s)".formatted(step, rows.formatted("Int.abs(cur)")))) {
            assertTrue(Proposition.leavesSomethingUnread(stated(plain, compared(walked))),
                    walked);
        }
        for (String walked : List.of("List.fold(%s, 0, %s)".formatted(step, rows.formatted("1")),
                "List.fold(%s, pay, %s)".formatted(step, rows.formatted("1")),
                "List.fold(%s, 0, %s)".formatted(step, rows.formatted("cur")))) {
            assertFalse(Proposition.leavesSomethingUnread(stated(plain, compared(walked))),
                    walked);
        }
        // Rows of a type that holds an invariant are the rows of the walk above where the
        // invariant is shown to hold of what each is handed, and are not where it cannot be shown
        // from what is handed. A constant it refuses is no model: the compile refuses it.
        String walked = "List.fold(%s, 0, %s)".formatted(step, rows.formatted("1"));
        assertEquals(stated(plain, compared(walked)), stated(held, compared(walked)));
        String unknown = "List.fold(%s, 0, %s)".formatted(step, rows.formatted("cur"));
        assertNotEquals(stated(plain, compared(unknown)), stated(held, compared(unknown)));
    }

    /**
     * A row a helper builds is worked out before any application as the row written out would be,
     * but only where everything the helper runs ends no run: a {@code let} whose value is not used
     * in the row it answers is run all the same.
     */
    @Test
    void aRowBuiltByAHelperIsSkippedOverOnlyWhereTheHelperRunsNothingThatMayEndTheRun() {
        String step = "(acc, r) -> if r.lowerBound <= pay then r.grade else acc";
        String rows = "[ rowAt(pay), rowAt(2) ]";
        String safe = """
                data Row = { grade: Int, lowerBound: Int }
                let rowAt (n: Int): Row = {
                    let spare = n
                    Row { grade = 1, lowerBound = 100 }
                }""";
        String ends = safe.replace("let spare = n", "let spare = 100 / n");
        String held = safe.replace("data Row = { grade: Int, lowerBound: Int }",
                "data Row = { grade: Int, lowerBound: Int }\n    invariant grade >= 0");
        String walked = "List.fold(%s, 0, %s)".formatted(step, rows);
        assertFalse(Proposition.leavesSomethingUnread(stated(safe, compared(walked))));
        assertFalse(Proposition.leavesSomethingUnread(stated(held, compared(walked))));
        // The helper that can end the run states the run it ends, which the one that cannot does not.
        assertNotEquals(stated(safe, compared(walked)), stated(ends, compared(walked)));

        // A helper hands its argument to the row, and an invariant that cannot be shown of an
        // input is not taken as held.
        String plainOf = "data Row = { grade: Int, lowerBound: Int }\n"
                + "let rowOf (g: Int): Row = Row { grade = g, lowerBound = 100 }";
        String heldOf = plainOf.replace("lowerBound: Int }",
                "lowerBound: Int }\n    invariant grade >= 0");
        // What a let binds is what its body is asked about, so a row built through one is the row
        // built without it.
        String through = "\nlet through (n: Int): Row = {\n    let k = n\n    rowOf(k)\n}";
        for (String row : List.of("rowOf(1)", "through(1)")) {
            String rowsOf = "List.fold(%s, 0, [ %s, rowOf(2) ])".formatted(step, row);
            assertEquals(stated(plainOf + through, compared(rowsOf)),
                    stated(heldOf + through, compared(rowsOf)), row);
        }
        String unproven = "List.fold(%s, 0, [ rowOf(cur), rowOf(2) ])".formatted(step);
        assertNotEquals(stated(plainOf, compared(unproven)), stated(heldOf, compared(unproven)));
    }

    /**
     * Whether the walk is skipped over does not turn on how its seed is spelled. A seed that is the
     * same value is written inline, bound to a name, or answered by a helper, and each of them
     * runs whatever the seed runs: a {@code let} whose value the seed does not use, and the fields
     * of a construction that an access takes one of. Where that cannot end a run the walk is read
     * as it is with a plain seed, and where it can it is not.
     */
    @Test
    void aSeedIsSkippedOverOnlyWhereWhatItRunsEndsNoRunHoweverItIsSpelled() {
        String step = "(acc, r) -> if r.lowerBound <= pay then r.grade else acc";
        // What the walk is worked out from: the seed, the grade of a row, and the container, each
        // a place that takes a value of its type in the place of PLACED.
        List<Place> places = List.of(
                new Place("seed", "List.fold(%s, PLACED, %s)".formatted(step, ASCENDING), "0",
                        "Int"),
                new Place("row", ("List.fold(%s, 0, [ Row { grade = PLACED, lowerBound = 100 },"
                        + " Row { grade = 2, lowerBound = 200 } ])").formatted(step), "0", "Int"),
                new Place("container", "List.fold(%s, 0, PLACED)".formatted(step), ASCENDING,
                        "List<Row>"));
        // What is run on the way to the value, whether or not the value uses it: a let, a
        // construction an access takes one field of, and a comparison inside a branch.
        List<String> wrappers = List.of("{\n    let spare = EFFECT\n    PAYLOAD\n}",
                "Row { grade = PAYLOAD, lowerBound = EFFECT }.grade",
                "if EFFECT >= 0 then PAYLOAD else PAYLOAD");
        for (Place place : places) {
            Proposition selected = stated(compared(
                    place.fold().replace("PLACED", place.payload())));
            for (String wrapper : wrappers) {
                if (wrapper.startsWith("Row {") && !place.payload().equals("0")) {
                    continue;
                }
                for (boolean ends : List.of(false, true)) {
                    String wrapped = wrapper.replace("PAYLOAD", place.payload());
                    String used = wrapped.replace("EFFECT", ends ? "Int.abs(cur)" : "cur");
                    String declarations = "data Row = { grade: Int, lowerBound: Int }\n"
                            + "let valueOf (n: Int): %s = ".formatted(place.type())
                            + wrapped.replace("EFFECT", ends ? "Int.abs(n)" : "n");
                    Map<String, String> spelled = new LinkedHashMap<>();
                    spelled.put("inline", compared(place.fold().replace("PLACED", used)));
                    spelled.put("named", "let held = %s\n%s".formatted(used,
                            compared(place.fold().replace("PLACED", "held"))));
                    spelled.put("helper", compared(
                            place.fold().replace("PLACED", "valueOf(cur)")));
                    for (Map.Entry<String, String> one : spelled.entrySet()) {
                        Proposition stated = stated(declarations, one.getValue());
                        String label = place.name() + " " + one.getKey() + " " + used;
                        if (ends) {
                            assertNotEquals(selected, stated, label);
                        } else {
                            assertEquals(selected, stated, label);
                        }
                    }
                }
            }
        }
    }

    /**
     * A construction that reads no input is the same on every run, but that is not a proof that
     * its invariant holds: the compile accepts a table of constants whose whole-table invariant
     * the constants break, and leaves the check to the run. So a table is read as the rows it
     * holds only where the invariant is shown, and not because the table reads nothing.
     */
    @Test
    void aTableOfConstantsIsNotReadAsItsRowsOnTheStrengthOfReadingNoInput() {
        String broken = """
                module demo

                data Row = { grade: Int, lowerBound: Int }
                data Table = List<Row>
                    invariant distinctGrades = List.allDistinctBy(.grade, value)
                let rowOf (g: Int, lo: Int): Row = Row { grade = g, lowerBound = lo }
                let table = Table([ rowOf(1, 100), rowOf(1, 200), rowOf(3, 300) ])

                behavior f : (cur: Int, pay: Int) -> Int
                let f (cur, pay) = List.length(table.value)
                """;
        Compilation compilation = Compilation.ofSource(broken, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the compile leaves this table to the run");

        String step = "(acc, r) -> if r.lowerBound <= pay then r.grade else acc";
        String declarations = """
                data Row = { grade: Int, lowerBound: Int }
                data Table = List<Row>
                    invariant distinctGrades = List.allDistinctBy(.grade, value)
                let rowOf (g: Int, lo: Int): Row = Row { grade = g, lowerBound = lo }
                let table = Table([ rowOf(1, 100), rowOf(1, 200), rowOf(3, 300) ])
                """;
        Proposition literal = stated(compared("List.fold(%s, 0, %s)".formatted(step, ASCENDING)));
        assertNotEquals(literal, stated(declarations,
                compared("List.fold(%s, 0, table.value)".formatted(step))));
    }

    /**
     * What a construction an {@code if} tests for is refused by is the branch the {@code if}
     * takes, so a seed that is such an {@code if} ends no run on a refusal.
     */
    @Test
    void aRefusalOfAConstructionAnIfTestsForEndsNoRun() {
        String step = "(acc, r) -> if r.lowerBound <= pay then r.grade else acc";
        String declarations = """
                data Row = { grade: Int, lowerBound: Int }
                    invariant grade >= 0
                """;
        String tested = "if Row { grade = cur, lowerBound = 100 } as row then 0 else 0";
        Proposition plain = stated(declarations, compared(
                "List.fold(%s, 0, %s)".formatted(step, ASCENDING)));
        assertEquals(plain, stated(declarations, compared(
                "List.fold(%s, %s, %s)".formatted(step, tested, ASCENDING))));
    }

    /** A place a walk is worked out from: the walk with PLACED where it goes, and what stands there
     *  when nothing is run on the way. */
    private record Place(String name, String fold, String payload, String type) {}

    private static String compared(String computed) {
        return "let computed = %s\nif computed < 2 then 1 else 0".formatted(computed);
    }

    /**
     * What the fold states is what the same table written as a chain of {@code if}s states: the
     * same proposition, so that which grade a bound selects is held and not only where the bounds
     * fall.
     */
    @Test
    void theFoldStatesWhatTheChainOfIfsStates() {
        for (String condition : List.of("computed < 2", "computed - cur < 2",
                "Int.abs(computed - cur) < 2")) {
            Proposition folded = stated("""
                    let computed = List.fold((acc, r) -> if r.lowerBound <= pay then r else acc,
                        Row { grade = 0, lowerBound = 0 }, %s).grade
                    if %s then 1 else 0""".formatted(ASCENDING, condition));
            assertEquals(stated("""
                    let computed = %s
                    if %s then 1 else 0""".formatted(BY_HAND, condition)), folded, condition);
            assertFalse(Proposition.leavesSomethingUnread(folded), condition);
        }
    }

    /** The rows in the order they are written: the last one met is the one kept. */
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

    /** A seed no form says keeps the reason it has. */
    @Test
    void aSeedNoFormSaysKeepsItsReason() {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data Row = { grade: Int, lowerBound: Int }
                data Ok
                data No
                let table: List<Row> = %s
                behavior f : (cur: Int, pay: Int) -> Ok | No
                let f (cur, pay) = {
                    let computed = List.fold((acc, r) -> if r.lowerBound <= pay then r.grade else acc,
                        cur * pay, table)
                    guard computed < 2 else No
                    Ok
                }
                """.formatted(ASCENDING), "Main");
        assertTrue(notRead(measure(compilation, "f")).toString().contains("NON_AFFINE_PRODUCT"));
    }

    /** A table an input decides is no step function written down. */
    @Test
    void aTableTheInputDecidesIsNotAStepFunction() {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data Row = { grade: Int, lowerBound: Int }
                data Ok
                data No
                behavior f : (pay: Int, rows: List<Row>) -> Ok | No
                let f (pay, rows) = {
                    let computed = List.fold((acc, r) -> if r.lowerBound <= pay then r else acc,
                        Row { grade = 0, lowerBound = 0 }, rows).grade
                    guard computed < 2 else No
                    Ok
                }
                """, "Main");
        assertFalse(notRead(measure(compilation, "f")).isEmpty());
    }

    private static PartitionEvidence measured(String table, String selects, String condition) {
        return measure(Compilation.ofSource("""
                module demo

                data Row = { grade: Int, lowerBound: Int }
                data Ok
                data No
                let table: List<Row> = %s
                let rowFor (monthly: Int): Row =
                    List.fold((acc, r) -> if %s then r else acc,
                        Row { grade = 0, lowerBound = 0 }, table)
                behavior f : (cur: Int, pay: Int) -> Ok | No
                let f (cur, pay) = {
                    let computed = rowFor(pay).grade
                    guard %s else No
                    Ok
                }
                """.formatted(table, selects, condition), "Main"), "f");
    }

    private static PartitionEvidence measuredByHand(String grade, String condition) {
        return measure(Compilation.ofSource("""
                module demo

                data Ok
                data No
                behavior f : (cur: Int, pay: Int) -> Ok | No
                let f (cur, pay) = {
                    let computed = %s
                    guard %s else No
                    Ok
                }
                """.formatted(grade, condition), "Main"), "f");
    }

    /** What the condition of the one fork that ends a body written {@code body} states. */
    private static Proposition stated(String body) {
        return stated("data Row = { grade: Int, lowerBound: Int }", body);
    }

    /** The same, over a declaration of {@code Row} as given. */
    private static Proposition stated(String row, String body) {
        Compilation compilation = Compilation.ofSource("""
                module demo

                %s

                behavior f : (cur: Int, pay: Int) -> Int
                let f (cur, pay) = {
                %s
                }
                """.formatted(row, body.indent(4).stripTrailing()), "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList(),
                () -> "the model compiles: " + body);
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

    private static PartitionEvidence measure(Compilation compilation, String behavior) {
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation.db().ask(new Adequacy.Coverage("demo")).value().get(behavior);
    }

    private static List<String> notRead(PartitionEvidence measured) {
        return measured.notRead().stream()
                .map(each -> each.at() + ": " + each.reason())
                .distinct()
                .sorted()
                .collect(Collectors.toList());
    }

    private static List<String> classesOf(PartitionEvidence measured, String path) {
        if (!(measured.partitioned()
                instanceof Measurement.Complete<List<PartitionEvidence.AxisCoverage>> complete)) {
            throw new AssertionError("the partition was measured: " + measured.partitioned());
        }
        return complete.value().stream()
                .filter(axis -> axis.path().equals(path))
                .flatMap(axis -> axis.classes().stream())
                .toList();
    }
}
