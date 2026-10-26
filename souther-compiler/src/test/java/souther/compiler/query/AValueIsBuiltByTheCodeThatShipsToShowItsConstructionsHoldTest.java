package souther.compiler.query;

import org.junit.jupiter.api.Test;

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
