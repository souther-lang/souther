package souther.compiler.conformance;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticPlace;
import souther.compiler.diag.Located;
import souther.compiler.diag.Primary;
import souther.compiler.diag.QuotedFrom;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourceProvenance;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.MeaningsOfABody;
import souther.compiler.meaning.Proposition;
import souther.compiler.partition.MeaningsOfABodyReading;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.function.Consumer;

/**
 * The documents a corpus is held against, written the same way every time.
 *
 * <p>Split because they churn for different reasons. What the compiler answered about a
 * model changes when the compiler's answers change, which is the whole point of keeping it; what a
 * diagnostic says changes when someone rewords a message, which is held by the test that owns that
 * rule and would otherwise rewrite the corpus every time.
 */
final class ConformanceSnapshot {

    /** Stood in for the version, which moves for reasons unrelated to what the compiler answered. */
    private static final String VERSION_PLACEHOLDER = "<version>";

    private ConformanceSnapshot() {
    }

    /**
     * What this compiler answered about the corpus, as the report writes it.
     *
     * <p>The whole document rather than a summary of it. Whether the rows are adequate is one bit,
     * and which class was covered and which branch ran is underneath — a change that leaves the bit
     * alone while swapping what it covers shows nowhere else.
     */
    static String report(ConformanceCorpus.Analysed analysed) {
        AdequacyReport report = analysed.report();
        SourceRendering rendering = new SourceRendering(analysed.corpus().names(),
                analysed.compilation().texts());
        return report.json(rendering).replace("\"" + report.compilerVersion() + "\"",
                "\"" + VERSION_PLACEHOLDER + "\"") + System.lineSeparator();
    }

    /**
     * Every part of a condition the corpus writes that the reading of what it means stopped at, and
     * why, one line each.
     *
     * <p>Its own document because what it records moves on its own. A rule added to that reading
     * takes a part this lists and turns it into something read, and a report may show nothing of
     * that where no reader of the proposition has a use for the part yet; here it is a line gone,
     * with the reason it had. A reason that changes for a part still unread is a line that changes,
     * which is how an obligation renamed is told from one met.
     */
    static String unread(ConformanceCorpus.Analysed analysed) {
        Compilation compilation = analysed.compilation();
        List<String> lines = new ArrayList<>();
        for (String module : compilation.modules()) {
            Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
            Map<String, InputDomain> inputs =
                    compilation.db().ask(new Adequacy.Inputs(module)).value();
            if (checked == null || inputs == null) {
                continue;
            }
            RuleReadingSource rules = RuleReadings.of(compilation, module);
            inputs.forEach((behavior, input) -> {
                AnalysisBody analysis = checked.analysisBodies().get(behavior);
                if (analysis == null) {
                    return;
                }
                InputReading reading = input.reading(rules);
                MeaningsOfABody meanings = MeaningsOfABodyReading.of(analysis, () -> reading,
                        InputReads.ofParametersWhereCallsStand(input.parameterReads(),
                                input.declared(rules),
                                ElementBindings.of(analysis, rules.newtypes()),
                                input.dependencies()),
                        rules.symbols(), rules.newtypes());
                meanings.stated().forEach((site, meaning) -> unreadIn(meaning.states(),
                        unread -> lines.add(module + "." + behavior + " " + site + " #"
                                + unread.ordinal() + ": " + unread.why())));
            });
        }
        lines.sort(String::compareTo);
        StringBuilder out = new StringBuilder();
        lines.forEach(line -> out.append(line).append(System.lineSeparator()));
        return out.toString();
    }

    /** Each part of {@code stated} nothing read, to {@code into}. */
    private static void unreadIn(Proposition stated, Consumer<Proposition.Unread> into) {
        switch (stated) {
            case Proposition.Unread unread -> into.accept(unread);
            case Proposition.All all -> all.parts().forEach(part -> unreadIn(part, into));
            case Proposition.Any any -> any.parts().forEach(part -> unreadIn(part, into));
            case Proposition.OnAnApplication applications ->
                    applications.each().forEach(each -> unreadIn(each, into));
            case Proposition.Some some -> unreadIn(some.ofTheElement(), into);
            default -> { }
        }
    }

    /**
     * The rows this compiler offers an author over the corpus, as {@code souther examples
     * --generate} prints them.
     *
     * <p>Its own document beside the report, because the two are answers to different questions and
     * move for different reasons. The report says what the rows cover; this says what work the
     * compiler can hand somebody about what they do not, and a change that leaves every count where
     * it was while composing a different value shows in neither the report nor a fixture written for
     * one rule.
     *
     * <p>What the command offers, which is the whole account: the rows for what a combination of
     * classes leaves uncovered and the rows at the edges a rule draws, the latter composed by
     * putting a value through this module's own decoders.
     */
    static String generated(ConformanceCorpus.Analysed analysed) {
        SourceRendering rendering = new SourceRendering(analysed.corpus().names(),
                analysed.compilation().texts());
        // Every module and every behavior, which is what the command does when it is told no
        // narrower.
        return "// --generate" + System.lineSeparator()
                + GeneratedRows.of(analysed.compilation(), null, null, rendering).text();
    }

    /**
     * Everything the compiler said about the corpus, one line each.
     *
     * <p>Without the message. Where each of them is written is what a reader of a difference needs
     * to go and look, and it is the half that does not move when a sentence is rewritten.
     *
     * <p>Where a report points is asked case by case rather than through one accessor answering
     * "the region, if there is one" — {@link Primary} has four cases and three of them are not a
     * region, and a renderer that read them as one absence would write the same line for a report
     * about the standard library and one about nothing at all.
     */
    static String diagnostics(ConformanceCorpus.Analysed analysed) {
        SourceRendering rendering = new SourceRendering(analysed.corpus().names(),
                analysed.compilation().texts());
        List<String> lines = new ArrayList<>();
        for (Located located : analysed.said()) {
            Diagnostic diagnostic = located.diagnostic();
            String code = diagnostic.code() == null ? "<uncoded>" : diagnostic.code();
            lines.add(diagnostic.severity().name().toLowerCase(Locale.ROOT) + " " + code + " "
                    + where(diagnostic.primary(), rendering));
        }
        return lines.isEmpty() ? "" : String.join(System.lineSeparator(), lines)
                + System.lineSeparator();
    }

    private static String where(Primary primary, SourceRendering rendering) {
        return switch (primary) {
            case Primary.InSource(DiagnosticPlace.InSource place) -> at(place.region(), rendering);
            case Primary.InAnUnnamedText(var unnamed) -> "in an unnamed text "
                    + line(unnamed.region(), rendering.layouts());
            case Primary.Unavailable(SourceProvenance from) -> "in " + from;
            case Primary.Nowhere() -> "nowhere";
        };
    }

    private static String at(Region region, SourceRendering rendering) {
        // A place a reader is sent to names the source it is in, which `DiagnosticPlace.InSource`
        // refuses to be built without — so the one case here is the only one there is.
        String file = region.start().quotedFrom()
                instanceof QuotedFrom.ASourceThisCompileHolds(var source)
                ? rendering.names().nameOf(source)
                : "<unnamed>";
        return (file == null ? "<unnamed>" : file) + ":" + line(region, rendering.layouts());
    }

    private static String line(Region region, SourceLayouts layouts) {
        return String.valueOf(layouts.resolve(region.start()));
    }
}
