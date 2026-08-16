package souther.compiler.check;

import souther.compiler.diag.Located;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.source.SourceId;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two import lines asking for one spelling are one contest, whichever kind of line each is.
 *
 * <p>Where a claim came from is what makes it and settles nothing after that. A library import and
 * an import of a module this compilation has are two ways of asking for a name, and an author who
 * wrote one of each has written one spelling with two meanings exactly as an author who wrote two
 * of either has.
 *
 * <p>It was three rules. Two library lines were answered where library lines are read, two
 * user-module lines where a scope is assembled, and one of each by neither — so
 * {@code import List ( map )} beside {@code import app.other ( map )} silently took the user
 * module's, and the author was told the library import was unused. The mistaken program had a
 * meaning, and which one depended on the shape of the lines.
 */
class AContestBetweenImportsIsSettledTheSameWhereverTheClaimsCameFromTest {

    /** A module publishing a value under a spelling the standard library also publishes. */
    private static final String OTHER = """
            module app.other exposing ( map, filter )
            let map (x: Int) = x
            let filter (x: Int) = x
            """;

    /** What the author is told about {@code own.sou}, by code. */
    private static Set<String> saidAbout(String own) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("other.sou", OTHER);
        byId.put("own.sou", own);
        Compilation compilation = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        List<String> codes = new ArrayList<>();
        for (Located said : compilation.diagnostics().get(new SourceId("own.sou"))) {
            codes.add(said.diagnostic().code());
        }
        return Set.copyOf(codes);
    }

    /** Both claims are library ones. */
    @Test
    void twoLibraryLines() {
        assertTrue(saidAbout("""
                module app.own
                import Map ( insert )
                import Set ( insert )

                let a (xs: Int) = xs
                """).contains("E1508"), "one spelling, two things brought");
    }

    /** Both claims name modules this compilation has. */
    @Test
    void twoUserModuleLines() {
        assertTrue(saidAbout("""
                module app.own
                import app.other ( map )
                import app.other2 ( map )

                let a (xs: Int) = xs
                """).contains("E1504"), "the second module is not here, so that is what is said");
    }

    /**
     * One of each, which used to be answered by neither rule.
     *
     * <p>The case this test is written for. Both lines are fine on their own and both claim
     * {@code map}, so neither gets it — and the author is told so on a line, rather than left with
     * a program whose meaning came from the order the two rules happened to run in.
     */
    @Test
    void oneOfEach() {
        Set<String> codes = saidAbout("""
                module app.own
                import List ( map )
                import app.other ( map )

                let a (xs: Int) = xs
                """);

        assertTrue(codes.contains("E1508"),
                () -> "one spelling, two things brought: " + codes);
        assertTrue(!codes.contains("E1922"),
                () -> "and neither line is unused — both were asked for and neither won: " + codes);
    }

    /**
     * A use of the contested name says nothing more.
     *
     * <p>The spelling stands for nothing, which is what the import line already told the author.
     * Reported at the use as well, one mistaken pair of lines costs a report in every body that
     * writes the name.
     */
    @Test
    void aUseOfTheContestedNameIsNotReportedAgain() {
        Set<String> codes = saidAbout("""
                module app.own
                import List ( map )
                import app.other ( map )

                let a (xs: Int) = map(xs)
                let b (xs: Int) = map(xs)
                """);

        assertEquals(Set.of("E1508"), codes,
                () -> "said once, on the lines that made the contest: " + codes);
    }
}
