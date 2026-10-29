package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.RunRewrite;
import souther.compiler.coverage.WalkRewrites;
import souther.compiler.meta.ModulePath;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A walk over a list that is one list on every run, and that no run took a second element of, owes
 * no rewrite, wherever the rewrites it owes are asked: in the account of the rows written, and in
 * the choice of a row to offer.
 *
 * <p>Each of those two reads what the rows did through {@link Adequacy#walkedNoFurtherIn}, and
 * each is held here by what it comes to, with a walk a row did go past as the control: a reading
 * that was never handed what the rows did would owe the first walk what it owes the second.
 */
class AWalkNoRunWentPastItsFirstElementOwesNoRewriteTest {

    private static final String MODEL = """
            module repro.fixed

            behavior fixed : (n: Int) -> Int

            let fixed (n) = List.fold((acc, x) -> acc + x, n, List.filter(x -> x > 5, [1, 9]))

            example fixed
                | "five" : (5) -> 14

            behavior open : (xs: List<Int>) -> Int

            let open (xs) = List.fold((acc, x) -> acc + x, 0, xs)

            example open
                | "one" : ([5]) -> 5
                | "two" : ([1, 2]) -> 3
            """;

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSources(List.of(MODEL), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model under test compiles");
        return compilation;
    }

    @Test
    void aRowIsNotOfferedARewriteOfAWalkNoRunWentPast() {
        Compilation compilation = compiled();

        assertEquals(0, ofWalks(ComposedRows.rewritesThrough(compilation, "fixed", "five")),
                "the one list of the walk was taken no further than its first element");
        assertEquals(true, ofWalks(ComposedRows.rewritesThrough(compilation, "open", "two")) > 0,
                "the control: a run took a second element of this walk");
    }

    private static long ofWalks(List<RunRewrite> rewrites) {
        return rewrites.stream().filter(WalkRewrites.Rewrite.class::isInstance).count();
    }

    @Test
    void theAccountOfTheRowsOwesNoRewriteOfAWalkNoRunWentPast() {
        Compilation compilation = compiled();
        String module = compilation.modules().getFirst();

        Map<String, List<ReplacementReading.Account>> accounts =
                compilation.db().ask(new Replacements.Readings(module)).value();

        assertEquals(true, accountsOfWalks(accounts.get("open")) > 0,
                "the control: the walk a run went past is owed its rewrites");
        assertEquals(0, accountsOfWalks(accounts.get("fixed")),
                "and the walk none went past is owed none");
    }

    private static long accountsOfWalks(List<ReplacementReading.Account> accounts) {
        return accounts.stream()
                .filter(each -> each.written() instanceof ReplacementAsWritten.OfAWalk).count();
    }
}
