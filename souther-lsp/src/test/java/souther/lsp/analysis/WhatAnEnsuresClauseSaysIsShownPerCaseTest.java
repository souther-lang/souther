package souther.lsp.analysis;

import souther.lsp.protocol.Hover;
import souther.lsp.protocol.Position;
import org.junit.jupiter.api.Test;

import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an editor is shown on an {@code ensures} clause.
 *
 * <p>A rule is about one case, and what {@code value} is differs between cases, so what the check can
 * make of a clause is not one answer. Shown per rule, an author reading the clause reads which of its
 * cases the check carries and which of them it only holds when the behavior answers; shown as one, a
 * clause whose cases are read to different depths would say the wrong thing about one of them.
 *
 * <p>And a case no rule names is shown on the behavior. There is no wildcard arm, so nothing being
 * stated about a case is the declaration speaking — which a reader can only see by reading every
 * clause and comparing it against the answer's cases.
 */
class WhatAnEnsuresClauseSaysIsShownPerCaseTest {

    private final Analyzer analyzer = new Analyzer();

    private static final String SRC = """
            module demo exposing ( Id, Found, Missing, findIt )

            data Id      = { n: Int, label: String }
            data Found   = { n: Int }
            data Missing = { asked: String }

            behavior findIt : (id: Id) -> Found | Missing
                constructs Found, Missing
                ensures Found   -> value.n == id.n
                      | Missing -> String.startsWith(id.label, value.asked)

            let findIt (id) =
                if id.n > 0 then Found { n = id.n } else Missing { asked = id.label }
            """;

    private Optional<Hover> hover(String source, int line, int character) {
        ModuleGraph graph = ModuleGraph.of(Map.of("file:///demo.sou", source));
        return analyzer.hover("file:///demo.sou", source, new Position(line, character), graph);
    }

    @Test
    void aClauseSaysWhatTheCheckReadsOfEachOfItsCases() {
        // inside the clause, on the arm for `Found`
        Optional<Hover> hover = hover(SRC, 8, 20);

        assertTrue(hover.isPresent());
        String shown = hover.get().contents();
        assertTrue(shown.contains("`Found`") && shown.contains("derivable"), shown);
        assertTrue(shown.contains("`Missing`") && shown.contains("exact match"), shown);
    }

    /** The same clause read from its other arm is the same clause: a hover is about what is written
     *  there, and both arms are written under one {@code ensures}. */
    @Test
    void theOtherArmOfOneClauseSaysTheSame() {
        assertTrue(hover(SRC, 9, 20).map(Hover::contents)
                .filter(shown -> shown.contains("`Found`") && shown.contains("`Missing`"))
                .isPresent());
    }

    /** Two cases under one arrow are two rules, and both are shown. The words are the same and what
     *  they are read of is not, so a reader is told about each case rather than about the arrow. */
    @Test
    void twoCasesUnderOneArrowAreBothShown() {
        String source = """
                module demo exposing ( Id, Found, Missing, findIt )

                data Id      = { n: Int }
                data Found   = { n: Int }
                data Missing = { n: Int }

                behavior findIt : (id: Id) -> Found | Missing
                    constructs Found, Missing
                    ensures Found | Missing -> value.n == id.n

                let findIt (id) =
                    if id.n > 0 then Found { n = id.n } else Missing { n = id.n }
                """;

        Optional<Hover> hover = hover(source, 8, 30);

        assertTrue(hover.isPresent());
        String shown = hover.get().contents();
        assertTrue(shown.contains("`Found`") && shown.contains("`Missing`"), shown);
    }

    @Test
    void aBehaviorSaysWhichOfItsCasesNothingIsStatedAbout() {
        String source = SRC.replace(
                "      | Missing -> String.startsWith(id.label, value.asked)\n", "");

        // over the behavior's name
        Optional<Hover> hover = hover(source, 6, 10);

        assertTrue(hover.isPresent());
        assertTrue(hover.get().contents().contains("Nothing is stated about `Missing`"),
                hover.get().contents());
    }

    @Test
    void aBehaviorEveryCaseOfWhichIsSpokenForSaysNothingOfTheKind() {
        Optional<Hover> hover = hover(SRC, 6, 10);

        assertTrue(hover.isPresent());
        assertFalse(hover.get().contents().contains("Nothing is stated about"),
                hover.get().contents());
    }

    /** Outside a clause the hover is what it was: this one has something semantic to say only where
     *  a rule is written. */
    @Test
    void hoverOutsideAClauseStillShowsTheSignature() {
        Optional<Hover> hover = hover(SRC, 3, 5);   // over `Found`

        assertTrue(hover.isPresent());
        assertTrue(hover.get().contents().contains("data Found"), hover.get().contents());
    }
}
