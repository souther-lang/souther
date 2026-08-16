package souther.compiler;

import souther.compiler.diag.Located;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.source.SourceId;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An {@code import} line this compiler cannot read is one thing the author is told, and the rest of
 * the file is still read.
 *
 * <p>Three things an import can get wrong, and {@link souther.compiler.check.Exposing} answered one
 * of them and raised the other two. The one it answers already says why in its own words: thrown, it
 * escapes the question that asked for this module and takes every other file's diagnostics with it.
 * That holds for all three, and the two that raise are why a file with a mistaken import line
 * reported nothing else in it.
 *
 * <p>Measured on what the author is shown rather than on whether a compile succeeded. A file with an
 * unreadable import fails either way; what is wrong is that everything else the compiler found there
 * goes unsaid, and only reading the diagnostics tells the two apart.
 */
class AnImportLineThatCannotBeReadIsSaidWithoutTakingTheFileTest {

    /** A second mistake, in no way about the import, written into every source here. */
    private static final String A_SECOND_MISTAKE = "data Bad = { x: NoSuchTypeAnywhere }";

    /** The codes the author is shown about the one source. */
    private static Set<String> saidAbout(String source) {
        Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
        Set<String> codes = new LinkedHashSet<>();
        for (Located said : compilation.diagnostics().get(new SourceId("0"))) {
            codes.add(said.diagnostic().code());
        }
        return codes;
    }

    /** The line names something this compiler's library does not publish. */
    @Test
    void aNameTheLibraryDoesNotHaveIsSaidBesideTheRest() {
        Set<String> codes = saidAbout("""
                module app.own
                import List ( noSuchOperation )

                %s
                """.formatted(A_SECOND_MISTAKE));

        assertTrue(codes.contains("E1506"), "the import line is refused: " + codes);
        assertTrue(codes.contains("E1023"),
                "and the mistake beside it is still said: " + codes);
    }

    /** One bare name arrives from two library modules at once. */
    @Test
    void aNamePublishedByTwoModulesIsSaidBesideTheRest() {
        Set<String> codes = saidAbout("""
                module app.own
                import Map ( insert )
                import Set ( insert )

                %s
                """.formatted(A_SECOND_MISTAKE));

        assertTrue(codes.contains("E1508"), "the import line is refused: " + codes);
        assertTrue(codes.contains("E1023"),
                "and the mistake beside it is still said: " + codes);
    }

    /**
     * The third of the three, which was already answered rather than raised.
     *
     * <p>The control the other two are measured against. It is the same kind of failure on the same
     * line, and the only reason this file's other mistake survives it is that this one comes back as
     * a value.
     */
    @Test
    void aNameThatCollidesWithADeclarationIsSaidBesideTheRest() {
        Set<String> codes = saidAbout("""
                module app.own
                import List ( map )

                let map (x) = x
                %s
                """.formatted(A_SECOND_MISTAKE));

        assertTrue(codes.contains("E1508"), "the import line is refused: " + codes);
        assertTrue(codes.contains("E1023"),
                "and the mistake beside it is still said: " + codes);
    }
}
