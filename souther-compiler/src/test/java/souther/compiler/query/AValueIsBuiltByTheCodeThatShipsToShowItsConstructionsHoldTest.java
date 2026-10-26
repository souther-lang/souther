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
}
