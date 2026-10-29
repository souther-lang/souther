package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.WalkRewrites;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.SourceConstructOrigin;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * The rewrites a row is asked under when it is chosen are the ones the measure of the rows written
 * owes, and a fold the model's own rules limit to one element at most is neither.
 *
 * <p>Asked of the way rows are run, which is where a search for a row puts the question, with a
 * row that enters both folds of a behavior: only the fold nothing limits is asked.
 */
class ARowIsOfferedOnlyTheRewritesTheMeasureOwesTest {

    private static final String TWO_FOLDS = """
            module repro.pair

            data Few = List<Int>
                invariant atMost = List.length(value) <= 1

            data In = { few: Few, many: List<Int> }

            behavior total : (i: In) -> Int

            let total (i) =
                List.fold((acc, x) -> acc + x, 0, i.few.value)
                    + List.fold((acc, x) -> acc + x, 0, i.many)

            example total
                | "nothing" : (In { few = Few([]), many = [] }) -> 0
            """;

    @Test
    void aFoldTheRulesLimitToOneElementAtMostIsNotAskedWhenARowIsChosen() {
        Compilation compilation = Compilation.ofSources(List.of(TWO_FOLDS), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model under test compiles");

        List<SourceConstructOrigin> folds = ComposedRows.rewritesThrough(
                        compilation, "total", "nothing").stream()
                .map(each -> assertInstanceOf(WalkRewrites.Rewrite.class, each).walk())
                .toList();

        assertEquals(2, folds.size(), () -> "both rewrites of one fold: " + folds);
        assertEquals(1, folds.stream().distinct().count(),
                () -> "of one fold and not of two: " + folds);
    }
}
