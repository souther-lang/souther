package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Citation;
import souther.compiler.diag.SourceNameResolver;
import souther.compiler.diag.SourcePos;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.source.SourceId;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which of the findings a report prints are the ones a build refuses over, said on both surfaces.
 *
 * <p>The distinction is decided in one place and was written down in none. A report printed four
 * findings as four bullets of one shape, a build refused over three of them, and the count the
 * refusal gave pointed at a list with a different number of entries in it. An author reading it
 * either wrote rows for everything printed — more than the build asks, on a measure the language
 * deliberately chose not to gate — or wrote one and ran again to find out.
 *
 * <p>Both surfaces read {@link Adequacy.Finding#disposition()}, so what is marked here and what the
 * document says are the same answer rather than two readings of the finding kinds.
 */
class WhichFindingsABuildRefusesOverIsWrittenDownTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /**
     * The model the issue was written from.
     *
     * <p>Its point is the pair one line apart: a class no row uses is a gap a build refuses over, and
     * the same class of the same position being a class no row is in is not. Writing a row for `C`
     * closes both, so nothing here goes wrong by accident — which is what makes it the clearest
     * statement of two findings whose sentences differ by three words being printed as the same kind
     * of thing.
     */
    private static final String MODEL = """
            module m

            data Grade = A | B | C

            data Weight = Int
                invariant value > 0

            data Shipped = { grade: Grade, weight: Weight }
            data TooHeavy

            behavior ship : (grade: Grade, weight: Weight) -> Shipped | TooHeavy
                constructs Shipped, Weight

            let ship (grade, weight) = {
                guard weight <= Weight(100) else TooHeavy
                Shipped { grade = grade, weight = weight }
            }

            example ship
                | "an A parcel within the limit ships" : (A, Weight(50)) -> Shipped { grade = A, weight = Weight(50) }
                | "a B parcel within the limit ships" : (B, Weight(50)) -> Shipped { grade = B, weight = Weight(50) }
                | "over the limit is refused" : (A, Weight(101)) -> TooHeavy
            """;

    /**
     * What the mark means, kept against the answer the build acts on.
     *
     * <p>Counted rather than listed: the marks and the gaps are two projections of one list, and a
     * test naming the three sentences would go on passing where a fourth finding started being
     * refused over and nothing marked it.
     */
    @Test
    void theMarkedLinesAreTheGapsABuildRefusesOver() {
        AdequacyReport report = report();
        String human = report.human(SourceNameResolver.identity());

        assertEquals(report.adequacyGaps().size(), marked(human).size(), human);
        assertFalse(report.adequacyGaps().isEmpty(), "the model has gaps to mark:\n" + human);
    }

    /** The pair the issue is about: one class, two findings, one of them refused over. */
    @Test
    void twoFindingsAboutOneClassAreMarkedApart() {
        String human = report().human(SourceNameResolver.identity());

        assertTrue(human.contains("      ! no row uses `C`"), human);
        assertTrue(human.contains("      · no row is in `C`"), human);
    }

    /**
     * The legend, in the report rather than only in what the refusal prints.
     *
     * <p>A reader who did not pass {@code --strict} sees the marks and is told nothing about them,
     * and the count is the other half of what the refusal used to say on its own.
     *
     * <p>What the mark means, and not the verdict a refusal reaches. The two surfaces print one under
     * the other where a strict build got a human report, and a legend that repeated the verdict would
     * be one sentence twice.
     */
    @Test
    void theReportSaysHowManyItMarkedAndWhatTheMarkMeans() {
        AdequacyReport report = report();
        String human = report.human(SourceNameResolver.identity());

        assertTrue(human.contains(report.adequacyGaps().size()
                + " gaps marked `!`: what a strict build refuses over."), human);
    }

    /** A model with nothing to refuse over says nothing about a mark it did not write. */
    @Test
    void aReportWithNothingToMarkHasNoLegend() {
        Compilation compilation = Compilation.ofSource("""
                module n

                data Yes
                data No
                data Flag = Yes | No
                data Ask = { flag: Flag }
                data Res = { n: Int }

                behavior classify : (q: Ask) -> Res
                    constructs Res
                let classify (q) = Res { n = 1 }

                example classify
                    | (Ask { flag = Yes }) -> Res { n = 1 }
                    | (Ask { flag = No }) -> Res { n = 1 }
                """, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        AdequacyReport report = AdequacyReport.of(compilation);
        String human = report.human(SourceNameResolver.identity());

        assertTrue(report.adequacyGaps().isEmpty(), human);
        assertFalse(human.contains("marked `!`"), human);
        assertTrue(marked(human).isEmpty(), human);
    }

    /**
     * The document says what each finding is, so a consumer showing "these are the ones you must
     * fix" reads an answer rather than reimplementing the classification from the kinds.
     */
    @Test
    void theJsonCarriesEveryFindingAndWhatABuildDoesAboutIt() {
        AdequacyReport report = report();
        JsonNode ship = JSON.readTree(report.json(SourceNameResolver.identity()))
                .get("modules").get(0).get("behaviors").get(0);
        JsonNode findings = ship.get("findings");

        assertNotNull(findings, "the behavior's findings are published");
        assertEquals(report.findings().size(), findings.size());
        assertEquals(report.adequacyGaps().size(), refused(findings).size(), findings.toString());

        // The pair the issue is about, in the document. The position is written with the class
        // because two parameters of one type produce two findings a class name alone cannot tell
        // apart.
        assertEquals(List.of("C (in #1)"), subjects(findings, "input_case_unspecified"));
        assertEquals(List.of("C"), subjects(findings, "axis_class_uncovered"));
        assertEquals("refused", disposition(findings, "input_case_unspecified"));
        assertEquals("reported", disposition(findings, "axis_class_uncovered"));
    }

    /**
     * Two findings of one behavior that no other field tells apart.
     *
     * <p>A behavior with two {@code guard}s writes two arms labelled {@code else}, and the label is
     * what a finding's subject is — so kind, disposition, subject and code came out identical on
     * both, and which arm a reader was being told about could not be worked out from the document.
     * The place is what {@code branch.unreached} already tells them apart by, so it is written under
     * the same key and the two join.
     */
    @Test
    void twoArmsOfOneNameAreToldApartByWhereTheyAre() {
        Compilation compilation = Compilation.ofSource("""
                module a

                data Amount = Int
                    invariant value > 0

                data Req = { small: Amount, large: Amount }
                data Ok
                data TooSmall
                data TooLarge

                behavior check : (r: Req) -> Ok | TooSmall | TooLarge
                    constructs Amount

                let check (r) = {
                    guard r.small >= Amount(10) else TooSmall
                    guard r.large <= Amount(100) else TooLarge
                    Ok
                }

                example check
                    | "both fit" : (Req { small = Amount(20), large = Amount(50) }) -> Ok
                """, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        JsonNode check = JSON.readTree(
                        AdequacyReport.of(compilation).json(SourceNameResolver.identity()))
                .get("modules").get(0).get("behaviors").get(0);

        List<JsonNode> arms = new ArrayList<>();
        for (JsonNode each : check.get("findings")) {
            if ("arm_unreached".equals(each.get("kind").asString())) {
                arms.add(each);
            }
        }
        assertEquals(2, arms.size(), check.toString());
        assertEquals(List.of("else", "else"),
                arms.stream().map(a -> a.get("subject").asString()).toList());
        assertEquals(2, arms.stream().map(a -> a.get("at").toString()).distinct().count(),
                "two arms of one name are two places: " + arms);

        // The same places, under the same key, as the measure that already told them apart.
        List<String> unreached = new ArrayList<>();
        for (JsonNode each : check.get("branch").get("unreached")) {
            unreached.add(each.get("at").toString());
        }
        assertEquals(unreached.stream().sorted().toList(),
                arms.stream().map(a -> a.get("at").toString()).sorted().toList());
    }

    /** The eight whose place is the declaration the entry already names do not write it again. */
    @Test
    void aFindingCitedAtItsDeclarationWritesNoPlace() {
        JsonNode findings = JSON.readTree(report().json(SourceNameResolver.identity()))
                .get("modules").get(0).get("behaviors").get(0).get("findings");

        for (JsonNode each : findings) {
            assertFalse(each.has("at"), each.toString());
        }
    }

    /**
     * The three answers, on the two facts they come from.
     *
     * <p>Asked of the finding directly, because the middle answer is what a two-valued field would
     * lose: a kind a build refuses over, from a measurement that did not come to an answer, is not a
     * gap and is not a finding of a kind nobody gates on either. The report already says that one in
     * words, and a document that called it `reported` would say the measure decided something it did
     * not.
     */
    @Test
    void aDispositionIsTheKindAndTheMeasurementTogether() {
        assertEquals(Adequacy.Finding.Disposition.REFUSED,
                finding(Adequacy.Kind.BOUNDARY_UNMET, MeasurementStatus.COMPLETE).disposition());
        assertEquals(Adequacy.Finding.Disposition.UNDECIDED,
                finding(Adequacy.Kind.BOUNDARY_UNMET, MeasurementStatus.PARTIAL).disposition());
        assertEquals(Adequacy.Finding.Disposition.REPORTED,
                finding(Adequacy.Kind.AXIS_CLASS_UNCOVERED, MeasurementStatus.COMPLETE)
                        .disposition());
        assertEquals(Adequacy.Finding.Disposition.REPORTED,
                finding(Adequacy.Kind.AXIS_CLASS_UNCOVERED, MeasurementStatus.PARTIAL)
                        .disposition());
    }

    /** The one statement of what a build refuses over, with the older reading of it held to it. */
    @Test
    void theGapAnswerIsTheDispositionAndNotASecondReading() {
        for (Adequacy.Kind kind : Adequacy.Kind.values()) {
            for (MeasurementStatus status : MeasurementStatus.values()) {
                Adequacy.Finding f = finding(kind, status);
                assertEquals(f.disposition() == Adequacy.Finding.Disposition.REFUSED,
                        f.isAdequacyGap(), kind + " at " + status);
            }
        }
    }

    private static Adequacy.Finding finding(Adequacy.Kind kind, MeasurementStatus status) {
        return new Adequacy.Finding(kind, "b", status,
                Citation.of(new SourcePos(1, 1, new SourceId("s"))), List.of("x"));
    }

    private static AdequacyReport report() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return AdequacyReport.of(compilation);
    }

    private static List<String> marked(String human) {
        return human.lines().filter(line -> line.stripLeading().startsWith("! ")).toList();
    }

    private static List<JsonNode> refused(JsonNode findings) {
        List<JsonNode> out = new ArrayList<>();
        for (JsonNode each : findings) {
            if ("refused".equals(each.get("disposition").asString())) {
                out.add(each);
            }
        }
        return out;
    }

    private static List<String> subjects(JsonNode findings, String kind) {
        List<String> out = new ArrayList<>();
        for (JsonNode each : findings) {
            if (kind.equals(each.get("kind").asString())) {
                out.add(each.get("subject").asString());
            }
        }
        return out;
    }

    private static String disposition(JsonNode findings, String kind) {
        for (JsonNode each : findings) {
            if (kind.equals(each.get("kind").asString())) {
                return each.get("disposition").asString();
            }
        }
        throw new AssertionError("no finding of kind " + kind + " in " + findings);
    }
}
