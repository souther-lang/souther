package souther.compiler.cst;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a parse that has lost its place picks itself up again.
 *
 * <p>Which words open a construct is a fact about the language, and {@link TopLevelForm} has it.
 * Where to resume after a run of tokens nothing could read is not: it is what this parser does about
 * a mistake, and it is stated once, here in the parser, as a rule over the catalog rather than as a
 * second list of words.
 *
 * <p>The rule is that a header form does not stop a recovery. A file has one header and it is
 * written at the top; a {@code module} line further down is not the beginning of a file, so resuming
 * there would be resuming at something the parse is already past.
 */
class RecoveryStopsAtWhatMayFollowTheHeaderTest {

    @Test
    void aDefinitionAfterTheMistakeIsStillRead() {
        CstParser.Result parsed = CstParser.parse("""
                module m

                ???

                data A = { v: Int }
                """);
        assertTrue(kindsOf(parsed).contains(SyntaxKind.DATA_DEF),
                "the definition after the mistake was swallowed by it");
    }

    /**
     * An import may follow the header, so a recovery stops at one. It is read no further here — the
     * imports have been read by the time a body item is being looked for — and it becomes a mistake
     * of its own, which is what leaves two of them rather than one.
     */
    @Test
    void anImportStopsARecovery() {
        CstParser.Result parsed = CstParser.parse("""
                data A = { v: Int }

                ???

                import up ( a )
                """);
        assertEquals(2, count(parsed, SyntaxKind.ERROR_TOKEN),
                "the import was taken as more of the mistake in front of it");
    }

    /** A header form does not, so it is taken as more of the mistake it is written after. */
    @Test
    void aHeaderDoesNotStopARecovery() {
        CstParser.Result parsed = CstParser.parse("""
                data A = { v: Int }

                ???

                module m
                """);
        assertEquals(1, count(parsed, SyntaxKind.ERROR_TOKEN),
                "the parse resumed at a header, which is not where a file begins");
    }

    private static List<SyntaxKind> kindsOf(CstParser.Result parsed) {
        return parsed.root().childNodes().stream().map(SyntaxNode::kind).toList();
    }

    private static long count(CstParser.Result parsed, SyntaxKind kind) {
        return kindsOf(parsed).stream().filter(k -> k == kind).count();
    }
}
