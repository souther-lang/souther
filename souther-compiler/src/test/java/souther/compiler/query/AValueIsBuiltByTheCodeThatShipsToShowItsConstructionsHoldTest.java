package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.execute.EvaluationPolicy;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value takes nothing and is built where its module builds it, so what it breaks is the module's
 * to answer for. It is built here by the code that ships: a value that breaks an invariant is a
 * compile error, and one that does not shows that the constructions written in it hold.
 *
 * <p>The invariant is one about the whole list, which the compile cannot work out from the
 * constants beside it. That is why a value is built and the constants are not folded.
 */
class AValueIsBuiltByTheCodeThatShipsToShowItsConstructionsHoldTest {

    private static final String MODULE = """
            module demo

            data Row = { grade: Int, lowerBound: Int }
            data Table = List<Row>
                invariant distinctGrades = List.allDistinctBy(.grade, value)
            let rowOf (g: Int, lo: Int): Row = Row { grade = g, lowerBound = lo }
            let table = Table([ rowOf(1, 100), rowOf(%s, 200) ])

            behavior f : (cur: Int, pay: Int) -> Int
            let f (cur, pay) = List.length(table.value)
            """;

    @Test
    void aValueThatBreaksAnInvariantWhenItIsBuiltIsRefused() {
        Compilation compilation = Compilation.ofSource(MODULE.formatted("1"), "Main");
        compilation.answerEverything();
        List<String> said = compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList();
        assertEquals(List.of("E2010 TheValueBreaksAnInvariantWhenItIsBuilt[value=table]"), said);
    }

    @Test
    void aValueThatDoesNotShowsItsConstructionsHold() {
        Compilation compilation = Compilation.ofSource(MODULE.formatted("2"), "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors());
        var built = compilation.db().ask(new Output.BuiltValues("demo"));
        assertTrue(built.present());
        assertFalse(built.value().isEmpty(), "the table is written in a value that was built");
    }

    private static final String ROW = """
            module demo

            data Row = { grade: Int }
                invariant nonNegative = grade >= 0
            let sample%s

            behavior f : (cur: Int) -> Int
            let f (cur) = cur
            """;

    private static int constructionsBuildingRuns(String sample) {
        Compilation compilation = Compilation.ofSource(ROW.formatted(sample), "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList());
        var built = compilation.db().ask(new Output.BuiltValues("demo"));
        assertTrue(built.present());
        return built.value().size();
    }

    @Test
    void aValueThatReadsAnotherIsBuiltAsTheOtherOneIs() {
        String module = """
                module demo

                data Row = { grade: Int }
                    invariant nonNegative = grade >= 0
                data Table = List<Row>
                    invariant distinctGrades = List.allDistinctBy(.grade, value)
                let first = Row { grade = 1 }
                let table = Table([ first, Row { grade = %s } ])

                behavior f : (cur: Int) -> Int
                let f (cur) = List.length(table.value)
                """;
        Compilation broken = Compilation.ofSource(module.formatted("1"), "Main");
        broken.answerEverything();
        assertEquals(List.of("E2010 TheValueBreaksAnInvariantWhenItIsBuilt[value=table]"),
                broken.errors().stream()
                        .map(each -> each.diagnostic().code() + " " + each.diagnostic().said())
                        .toList());
    }

    /**
     * The carrier the abort leaves by is the one class for a broken invariant and for a division by
     * zero, so a build that ended by the second is not a value that breaks an invariant — and says
     * nothing of the constructions written in it.
     */
    @Test
    void aBuildThatEndsInSomethingOtherThanABrokenInvariantIsNotAViolation() {
        String module = """
                module demo

                data Row = { grade: Int }
                    invariant nonNegative = grade >= 0
                let zero = List.length([1]) - 1
                let sample = [Row { grade = 1 }, Row { grade = Int.floorMod(1, zero) }]

                behavior f : (cur: Int) -> Int
                let f (cur) = cur
                """;
        Compilation compilation = Compilation.ofSource(module, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList());
        var built = compilation.db().ask(new Output.BuiltValues("demo"));
        assertTrue(built.present());
        assertTrue(built.value().isEmpty(), "nothing was shown to hold: " + built.value());
    }

    /** A value is held to what a row is, so one that does not stop within it is left to the check
     *  that runs when the program does and shows nothing. */
    @Test
    void aBuildThatSpendsMoreThanARunMayIsNotDecided() {
        String module = """
                module demo

                data Counted = { n: Int }
                    invariant nonNegative = n >= 0
                let sample = Counted { n = List.length(List.rangeInclusive(1, 5000)) }

                behavior f : (cur: Int) -> Int
                let f (cur) = cur
                """;
        Compilation roomy = Compilation.ofSource(module, "Main");
        roomy.answerEverything();
        assertEquals(1, roomy.db().ask(new Output.BuiltValues("demo")).value().size(),
                "within the default, the value is built and its construction recorded");

        Compilation tight = Compilation.ofSource(module, "Main")
                .withEvaluationPolicy(EvaluationPolicy.DEFAULT.withStepLimit(100));
        tight.answerEverything();
        assertEquals(List.of(), tight.errors().stream()
                .map(each -> each.diagnostic().code()).toList());
        assertTrue(tight.db().ask(new Output.BuiltValues("demo")).value().isEmpty());
    }

    /**
     * A value several others read is built once and is the answer for itself: the values built
     * from it are not told they broke an invariant because it did.
     */
    @Test
    void aViolationIsReportedOnceAtTheValueThatBrokeIt() {
        String module = """
                module demo

                data Row = { grade: Int }
                    invariant nonNegative = grade >= 0
                data Table = List<Row>
                    invariant distinctGrades = List.allDistinctBy(.grade, value)
                let base = Table([ Row { grade = 1 }, Row { grade = 1 } ])
                let first = Row { grade = List.length(base.value) }
                let second = Row { grade = List.length(base.value) + 1 }

                behavior f : (cur: Int) -> Int
                let f (cur) = cur
                """;
        Compilation compilation = Compilation.ofSource(module, "Main");
        compilation.answerEverything();
        assertEquals(List.of("E2010 TheValueBreaksAnInvariantWhenItIsBuilt[value=base]"),
                compilation.errors().stream()
                        .map(each -> each.diagnostic().code() + " " + each.diagnostic().said())
                        .toList());
    }

    /**
     * Which values are built is not which values write a construction the build is known to run.
     * One that breaks an invariant in a branch it takes, or in a helper it calls, is as much a value
     * that breaks it when it is built.
     */
    @Test
    void aValueIsBuiltWhereverItBreaksTheInvariant() {
        String module = """
                module demo

                data Row = { grade: Int }
                data Table = List<Row>
                    invariant distinctGrades = List.allDistinctBy(.grade, value)
                let rowOf (g: Int): Row = Row { grade = g }
                let tableOf (g: Int): Table = Table([ rowOf(g), rowOf(g) ])
                %s

                behavior f : (cur: Int) -> Int
                let f (cur) = cur
                """;
        for (String value : List.of(
                "let table = if 1 > 0 then Table([ rowOf(1), rowOf(1) ])"
                        + " else Table([ rowOf(1), rowOf(2) ])",
                "let table = tableOf(1)")) {
            Compilation compilation = Compilation.ofSource(module.formatted(value), "Main");
            compilation.answerEverything();
            assertEquals(List.of("E2010 TheValueBreaksAnInvariantWhenItIsBuilt[value=table]"),
                    compilation.errors().stream()
                            .map(each -> each.diagnostic().code() + " " + each.diagnostic().said())
                            .toList(), value);
        }
    }

    @Test
    void aConstructionBuildingTheValueRunsIsRecorded() {
        assertEquals(1, constructionsBuildingRuns(" = Row { grade = 3 }"));
        assertEquals(1, constructionsBuildingRuns(" = [Row { grade = 3 }]"));
    }

    /**
     * Building the value ran no one of these: a function value is made and not applied, one branch
     * and one arm of a choice run and the others do not, and the right operand of an operator that
     * stops once its answer is settled runs only where the left does not settle it. Recording a
     * construction from any of them would say a build showed it holds when the build never ran it.
     */
    @Test
    void aConstructionBuildingTheValueDoesNotRunIsNotRecorded() {
        assertEquals(0, constructionsBuildingRuns(
                ": List<(Int) -> Row> = [(n) -> Row { grade = n }]"));
        assertEquals(0, constructionsBuildingRuns(
                " = if 1 > 2 then Row { grade = 1 } else Row { grade = 2 }"));
        assertEquals(0, constructionsBuildingRuns(
                " = [1 > 2 && Row { grade = 1 }.grade > 0]"));
    }
}
