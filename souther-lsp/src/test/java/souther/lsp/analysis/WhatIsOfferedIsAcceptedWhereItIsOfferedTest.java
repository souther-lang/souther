package souther.lsp.analysis;

import souther.compiler.Compiler;
import souther.compiler.diag.CompileException;
import souther.compiler.fmt.Skeleton;
import souther.lsp.protocol.CompletionItem;
import souther.lsp.protocol.Position;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What is offered, written where it was offered, is accepted there.
 *
 * <p>The claim is about what the skeleton settles and nothing else: how many parameters an
 * implementation takes and what the injected ones are called, and what a row has to supply before it
 * can run. Those are E1615 and E1908, and they are what is asserted. What a body computes and what a
 * row expects are not the skeleton's to know — it leaves holes exactly there — so the holes are
 * filled from the model this is written against rather than from something invented to fill them.
 *
 * <p>Filling is done through the hole positions the skeleton hands back, from the last to the first,
 * which is what a client does with them. A test that rebuilt the text itself would be asserting
 * against its own idea of the declaration rather than against the one that was offered.
 */
class WhatIsOfferedIsAcceptedWhereItIsOfferedTest {

    private static final String URI = "file:///m.sou";

    /** A model that compiles, whose one behavior depends on another and has a row that runs. */
    private static final String WHOLE = """
            module m

            data MemberId = String
            data Found = { id: MemberId }

            behavior findMember : (id: MemberId) -> Found

            behavior place : (id: MemberId) -> Found
                depends on findMember

            let place (id, findMember) = findMember(id)
            """;

    /** The same with the implementation taken away, which is where one is offered. */
    private static final String WITHOUT_THE_IMPLEMENTATION =
            WHOLE.replace("let place (id, findMember) = findMember(id)\n", "");

    @Test
    void theModelThisIsWrittenAgainstCompiles() {
        Compiler.compile(WHOLE);
    }

    /**
     * The implementation offered for a behavior takes what the checker holds one to.
     *
     * <p>Its body is the one the model had, since a body is what the skeleton does not know.
     */
    @Test
    void anOfferedImplementationIsAccepted() {
        String written = filled(offered(WITHOUT_THE_IMPLEMENTATION, "let place"),
                "id", "findMember(id)");
        assertEquals("let place (id, findMember) = findMember(id)\n", written);
        Compiler.compile(WITHOUT_THE_IMPLEMENTATION + "\n" + written);
    }

    /**
     * And an implementation that does not is refused, which is what makes the above an assertion.
     *
     * <p>The injected parameter is moved in front of the input it follows. Nothing else changes: the
     * same names, the same count, the same body.
     */
    @Test
    void anImplementationWrittenAnotherWayIsRefused() {
        String swapped = "let place (findMember, id) = findMember(id)\n";
        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compile(WITHOUT_THE_IMPLEMENTATION + "\n" + swapped));
        assertEquals("E1615", refused.code());
    }

    /** A row offered for a behavior supplies what the run needs of it. */
    @Test
    void anOfferedRowIsAccepted() {
        String written = filled(offered(WHOLE, "example place"),
                "MemberId(\"m-1\")", "Found { id = MemberId(\"m-1\") }",
                "Found { id = MemberId(\"m-1\") }");
        Compiler.compile(WHOLE + "\n" + written);
    }

    /**
     * And a row without it is refused for want of a stand-in.
     *
     * <p>The {@code with} the skeleton wrote is taken back out of the row it was offered in, so what
     * is being asserted is that writing it is what stopped E1908 rather than something else about
     * the row.
     */
    @Test
    void aRowWithoutWhatItSuppliesIsRefused() {
        String written = filled(offered(WHOLE, "example place"),
                "MemberId(\"m-1\")", "Found { id = MemberId(\"m-1\") }",
                "Found { id = MemberId(\"m-1\") }");
        String withoutTheStandin =
                written.replaceAll("\\s*with findMember = Found \\{ id = MemberId\\(\"m-1\"\\) \\}", "");
        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compile(WHOLE + "\n" + withoutTheStandin));
        assertEquals("E1908", refused.code());
    }

    /** The skeleton offered under {@code label} where {@code source} is the document. */
    private static Skeleton.Built offered(String source, String label) {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(URI, source);
        List<CompletionItem> items = new Analyzer().completions(URI,
                new Position((int) source.lines().count(), 0), ModuleGraph.of(sources));
        for (CompletionItem item : items) {
            if (item.label().equals(label)) {
                assertNotNull(item.writes(), label + " offered nothing to write");
                return item.writes();
            }
        }
        throw new AssertionError("nothing labelled " + label + " was offered");
    }

    /** {@code written} with each hole replaced, in the order the holes are written. */
    private static String filled(Skeleton.Built written, String... answers) {
        List<Skeleton.Placed> holes = new ArrayList<>(written.holes());
        assertEquals(answers.length, holes.size(),
                "the skeleton has " + holes.size() + " holes and " + answers.length
                        + " were answered: " + written.text());
        StringBuilder out = new StringBuilder(written.text());
        for (int i = holes.size() - 1; i >= 0; i--) {
            out.replace(holes.get(i).start(), holes.get(i).end(), answers[i]);
        }
        return out.toString();
    }
}
