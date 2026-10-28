package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticPlace;
import souther.compiler.diag.LabeledRegion;
import souther.compiler.diag.Located;
import souther.compiler.diag.Messages;
import souther.compiler.diag.QuotedFrom;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Locale;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A warning about a rewrite no row tells apart says which rewrite it is, by what tells it from the
 * other rewrites of the body — the facts the page and a composed row say it by, and none fewer.
 *
 * <p>Two forks of code this build holds no source of are told apart by the definition that wrote
 * each. Two values the body could answer are told apart by the row that came to each, which is
 * marked where it is written: a row written without a name is numbered within its source, and two
 * sources each have a first row.
 */
class ARewriteWarningSaysWhichRewriteItIsTest {

    @Test
    void twoForksOutOfSightAreSaidByTheDefinitionsThatWroteThem() {
        List<String> said = rewriteWarnings(List.of("""
                module example.spread

                behavior spread : (a: Int, b: Int) -> Int

                let spread (a, b) = Int.max(a, b) - Int.min(a, b)

                example spread
                    | (0, 0) -> 0
                    | (3, 3) -> 0
                """)).stream().map(d -> Messages.render(d.said(), Locale.ENGLISH)).toList();

        assertEquals(List.of(
                        "No row of `spread` would come out differently if the `else` arm of a fork"
                                + " of `souther.int.max`, which this build holds no source of,"
                                + " answered as the `then` arm.",
                        "No row of `spread` would come out differently if the `else` arm of a fork"
                                + " of `souther.int.min`, which this build holds no source of,"
                                + " answered as the `then` arm.",
                        "No row of `spread` would come out differently if its body answered what"
                                + " row `#1` answers whatever it was given."),
                said);
    }

    @Test
    void twoValuesAnsweredByRowsOfTwoSourcesAreMarkedWhereEachRowIs() {
        List<Diagnostic> warnings = rewriteWarnings(List.of("""
                module example.doubled

                data Ok = { n: Int }
                data Err
                data Outcome = Ok | Err

                behavior doubled : (n: Int) -> Outcome

                let doubled (n) = Ok { n = n * 2 }

                example doubled
                    | (0) -> Ok
                """, """
                examples for example.doubled

                example doubled
                    | (1) -> Ok
                """));

        // Both rows are the first of their source, so the sentence names `#1` twice; the marks
        // are what is left to tell the two apart, and they are in the two sources.
        assertEquals(2, warnings.size(), () -> "a warning for each value: " + warnings);
        Set<QuotedFrom> marked = warnings.stream()
                .flatMap(d -> d.secondary().stream())
                .filter(label -> Messages.render(label.said(), Locale.ENGLISH)
                        .equals("the value is the one this row came to"))
                .map(LabeledRegion::place)
                .map(place -> ((DiagnosticPlace.InSource) place).region().start().quotedFrom())
                .collect(Collectors.toSet());
        assertEquals(2, marked.size(),
                () -> "each warning marks its own row, in its own source: " + warnings);
    }

    private static List<Diagnostic> rewriteWarnings(List<String> sources) {
        Compilation compilation = Compilation.ofSources(sources, ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return compilation.warnings().stream()
                .map(Located::diagnostic)
                .filter(d -> "E1939".equals(d.code().toString()))
                .toList();
    }
}
