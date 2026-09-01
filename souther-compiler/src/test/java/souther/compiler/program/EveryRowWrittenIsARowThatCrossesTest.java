package souther.compiler.program;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Prepared;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Acceptance;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;
import souther.compiler.query.Shapes;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every row a module writes is a row an output is handed.
 *
 * <p>What must never happen is a row that could not be handed over arriving as no row. An output
 * would then read that a behavior has no rows and count a set it never walked as one it walked and
 * found empty — which is worse than being told nothing, because it is being told something false
 * about what the model says.
 *
 * <p>Counted rather than sampled, and counted against what was written rather than against a number
 * written here: a test holding a number of its own agrees with the model until someone edits one of
 * them.
 */
class EveryRowWrittenIsARowThatCrossesTest {

    /** Rows of every kind there is: named and unnamed, a whole value and a bare case, one that
     *  needs something stood in for, and one whose value is larger than a snapshot keeps. */
    private static final String MODULE = """
            module demo

            data Amount = Int
            data Rate = Int
            data Receipt = { total: Amount }
            data Refused = { why: String }
            data Count = Int

            behavior rateNow : () -> Rate

            behavior billFor : (a: Amount) -> Receipt | Refused constructs Receipt, Refused

            let billFor (a) =
                if a.value > 0 then Receipt { total = a } else Refused { why = "nothing" }

            behavior scaled : (a: Amount) -> Amount
                depends on rateNow
                constructs Amount

            let scaled (a, rateNow) = Amount(a.value * rateNow().value)

            behavior countOf : (xs: List<Int>) -> Count constructs Count

            let countOf (xs) = Count(List.length(xs))

            example billFor
                | "a bill" : (Amount(1)) -> Receipt { total = Amount(1) }
                | (Amount(0)) -> Refused

            example scaled
                | "with a rate" : (Amount(2)) with rateNow = Rate(3) -> Amount(6)

            example countOf
                | "a long list" : ([ %s ]) -> Count(65)
            """.formatted(sixtyFive());

    /**
     * The rows of the same behaviors, written where they outgrew the model.
     *
     * <p>A behavior's rows are written across its own file and any number of attached files, and
     * which of them a row is in is a fact about the row rather than something a reader picks
     * between. A count that read one source would be a count of some of them with nothing in it to
     * say so.
     */
    private static final String BESIDE = """
            examples for demo

            example billFor
                | "beside the model" : (Amount(3)) -> Receipt { total = Amount(3) }
                | (Amount(4)) -> Receipt { total = Amount(4) }
            """;

    private static String sixtyFive() {
        StringBuilder written = new StringBuilder();
        for (int i = 0; i < 65; i++) {
            written.append(i == 0 ? "" : ", ").append(i);
        }
        return written.toString();
    }

    @Test
    void everyRowWrittenIsARowThatCrosses() {
        List<String> sources = List.of(MODULE);

        assertEquals(written(sources), crossed(sources),
                "a row the compile read is a row an output is handed");
    }

    /** And the rows a module writes beside itself are among them. */
    @Test
    void andSoIsEveryRowWrittenInAnAttachedFile() {
        List<String> both = List.of(MODULE, BESIDE);

        assertEquals(written(both), crossed(both),
                "a row written in an attached file is a row an output is handed");
        assertEquals(written(List.of(MODULE)) + 2, written(both),
                "and the attached file's rows are two more than the model's own");
    }

    /** And the count is of something, so the comparisons above are not two zeroes. */
    @Test
    void andThereAreRowsToCount() {
        assertTrue(written(List.of(MODULE)) >= 4,
                () -> "the module writes " + written(List.of(MODULE)) + " rows");
    }

    /** What the sources write, read off the module as the compiler prepared it. */
    private static int written(List<String> sources) {
        Compilation compilation = Compilation.ofSources(sources, ModulePath.EMPTY);
        Acceptance.of(compilation);
        Db db = compilation.db();
        int rows = 0;
        for (String module : compilation.modules()) {
            Prepared prepared = db.ask(new Shapes.Prepared(module)).value();
            for (Prepared.Example block : prepared.forExamples().examples()) {
                rows += block.read().rows().size();
            }
        }
        return rows;
    }

    /** What an output is handed. */
    private static int crossed(List<String> sources) {
        List<CheckedRow> every = new ArrayList<>();
        for (CheckedModule module : CheckedProgram.of(sources).modules()) {
            for (CheckedBehavior behavior : module.behaviors()) {
                every.addAll(behavior.rows());
            }
        }
        return every.size();
    }
}
