package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.cst.CstParser;
import souther.compiler.diag.SourceRendering;
import souther.compiler.observe.Limits;
import souther.compiler.partition.Generator;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row offered stopping at a guard says so over it: which guard, and what each way past it came
 * to, in the words that kind of answer already has.
 *
 * <p>Over the row a reader completes, and not among the notes about places no row was found for.
 * The row is offered; what a reader needs is that it does not get past the guard and why.
 */
class ARowThatStopsAtAGuardSaysWhyOverItTest {

    /** A set handed a field of a value the module states, which the row names and does not move,
     *  at a string longer than an observation reads — so what was built there is nothing this can
     *  write, and nothing here composes a set that holds it. */
    private static final String ONLY_NAMED = """
            module example.settle

            data Plain
            data Express
            data Kind = Plain | Express

            data Request = { level: String, note: Int }

            data Other = { allowed: Set<String> }

            data Done = { n: Int }
            data Refused

            let usual = Request { level = "%s", note = 1 }

            behavior settle : (kind: Kind, other: Other, request: Request) -> Done | Refused
                constructs Done

            let settle (kind, other, request) = {
                guard Set.contains(request.level, other.allowed) else Refused
                match kind with
                    | Plain -> Done { n = 2 }
                    | Express -> Done { n = 3 }
            }
            """.formatted("x".repeat(Limits.DEFAULT.maxText() + 1));

    /** The row past the guard, with nothing to say about one. */
    private static final String GOES_ON = """
            module example.settle

            data Plain
            data Express
            data Kind = Plain | Express

            data Done = { n: Int }
            data Refused

            behavior settle : (kind: Kind, amount: Int) -> Done | Refused
                constructs Done

            let settle (kind, amount) = {
                guard amount > 0 else Refused
                match kind with
                    | Plain -> Done { n = amount }
                    | Express -> Done { n = amount + 500 }
            }
            """;

    private static String offered(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model under test compiles");
        return GeneratedRows.of(compilation, null, null,
                new SourceRendering(id -> "settle.sou", compilation.texts())).text();
    }

    /** The line just over the row named {@code name}. */
    private static String over(String block, String name) {
        List<String> lines = block.lines().toList();
        for (int at = 1; at < lines.size(); at++) {
            if (lines.get(at).startsWith("    | \"" + name + "\"")) {
                return lines.get(at - 1);
            }
        }
        throw new AssertionError("no row is named " + name + " in " + block);
    }

    /** The guard where it is written: its line in the source the row is offered for. */
    @Test
    void theRowSaysWhichGuardItStopsAt() {
        String block = offered(ONLY_NAMED);
        int line = ONLY_NAMED.lines().toList().indexOf(ONLY_NAMED.lines()
                .filter(each -> each.contains("guard ")).findFirst().orElseThrow()) + 1;
        String said = over(block, "kind=Plain");
        assertTrue(said.startsWith("// stops at the guard at settle.sou:" + line + ":"),
                () -> "over the row, the guard it stops at: " + block);
    }

    /**
     * And what the way past it came to, in the words its search has: nothing here composing one,
     * and never the model's word that the rules leave nothing there.
     */
    @Test
    void theWayPastIsSaidAsThisCompilerComposingNothing() {
        String said = over(offered(ONLY_NAMED), "kind=Plain");
        assertTrue(said.contains("way 1 past it: the value built at `request.level` cannot be"
                        + " written"),
                () -> "the word the search for the way came to: " + said);
        assertFalse(said.contains(GeneratedRows.why(
                        Generator.UnresolvedCombination.Reason.THE_RULES_LEAVE_NOTHING_THERE)),
                () -> "and not the model's word: " + said);
    }

    /** A row that goes on past the guard has nothing over it about one. */
    @Test
    void aRowPastTheGuardHasNothingSaidOverIt() {
        String block = offered(GOES_ON);
        assertFalse(over(block, "kind=Express").startsWith("// stops at"),
                () -> "nothing over a row that went on: " + block);
        assertTrue(over(block, "amount=x <= 0").startsWith("// stops at the guard at"),
                () -> "and the row that does stop is said to: " + block);
    }

    /**
     * A guard whose ways past the reading cannot write down is said as this compiler's shortfall,
     * and not as a guard no row goes past.
     */
    @Test
    void waysPastNotReadAreSaidAsThisCompilersAndNotAsTheModels() {
        String said = over(offered(GOES_ON.replace("guard amount > 0",
                "guard (if amount > 0 then amount else 0 - amount) > 4")), "kind=Express");
        assertTrue(said.contains("the ways past it could not be read off the body")
                        && said.contains("which does not make it a guard no row goes past"),
                () -> "the guard's ways were not read, said as such: " + said);
        assertFalse(said.contains("never comes out the way the block goes on"),
                () -> "and not as the model's word: " + said);
    }

    /** What is said over a row is a comment, so the block still parses. */
    @Test
    void whatIsSaidOverTheRowLeavesTheBlockSomethingAFileCanHold() {
        String block = offered(ONLY_NAMED);
        assertEquals(List.of(),
                CstParser.parse("examples for example.settle\n\n" + block).errors(),
                () -> "the block parses: " + block);
    }
}
