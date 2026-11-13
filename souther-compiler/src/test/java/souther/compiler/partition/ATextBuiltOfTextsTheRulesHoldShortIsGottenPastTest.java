package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.ObjectMapper;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.values.TextExtents;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A run to an equality over {@code v} builds a text of {@code v} on the way, which stops a run only
 * where that text, or one built on the way to it, is longer than a {@code String} holds. Where the
 * rules hold {@code v} short enough that none can be, it gets past at every value and the equality
 * is read at every value of {@code v}; one code point longer and it is not shown to.
 *
 * <p>Each pair is the longest {@code v} the bound ({@link TextsBuilt}) says every text fits at,
 * and one past it. With the length of a {@code String} {@code L}, two joined texts in canonical
 * form adding at most three code points, and a text growing at most four times once put in it:
 * {@code v ++ v} fits while {@code 2n + 3 <= L}.
 */
class ATextBuiltOfTextsTheRulesHoldShortIsGottenPastTest {

    private static final String NOT_SHOWN_REACHED = "relation_not_shown_reached_at_every_value";

    private static final String READ = "rule_relating_two_values";

    private static final long L = TextExtents.LONGEST_STRING;

    private static String model(String rule, String text) {
        return """
                module held

                data V = String%s

                behavior f : (v: V, ns: List<String>, up: Bool) -> Bool
                let f (V(v), ns, up) = {
                    let m = %s
                    List.any(own -> own == v, ns) || String.length(m) > 0
                }
                """.formatted(rule, text);
    }

    private static String atMost(long codePoints) {
        return " invariant String.length(value) <= " + codePoints;
    }

    /** Why {@code v} is not read, each reason once in the order the report gives them. */
    private static List<String> whyVIsNotRead(String source) {
        Compilation model = ACompiledModel.measured(source,
                Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        JsonNode report = new ObjectMapper().readTree(AdequacyReport.of(model)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        List<String> out = new ArrayList<>();
        for (JsonNode module : report.path("modules")) {
            for (JsonNode behavior : module.path("behaviors")) {
                for (JsonNode each : behavior.path("partition").path("notRead")) {
                    String reason = each.path("reason").asString();
                    if (each.path("position").asString().equals("v") && !out.contains(reason)) {
                        out.add(reason);
                    }
                }
            }
        }
        return out;
    }

    private static void reachedAtEveryValue(String source) {
        List<String> why = whyVIsNotRead(source);
        assertTrue(why.contains(READ) && !why.contains(NOT_SHOWN_REACHED),
                () -> source + " " + why);
    }

    private static void notShownReachedAtEveryValue(String source) {
        List<String> why = whyVIsNotRead(source);
        assertTrue(why.contains(NOT_SHOWN_REACHED), () -> source + " " + why);
    }

    /** Fits up to {@code longest} code points of {@code v} and not one past it. */
    private static void fitsUpTo(long longest, String text) {
        reachedAtEveryValue(model(atMost(longest), text));
        notShownReachedAtEveryValue(model(atMost(longest + 1), text));
    }

    /** Two texts joined, by the operator and by the operation: {@code 2n + 3}, and
     *  {@code n + 2 + 3} beside a text written out. A text no rule holds may be too long. */
    @Test
    void twoTextsJoinedFitWhereTheyAndASeamDo() {
        fitsUpTo((L - 3) / 2, "v ++ v");
        fitsUpTo(L - 5, "String.append(v, \"ab\")");
        notShownReachedAtEveryValue(model("", "v ++ \"ab\""));
    }

    /** Copies and a join of a list written out: three copies are {@code 3n} and two seams, two
     *  texts with a separator {@code 2n + 1} and a seam on each side of it. A list no rule holds
     *  may hold as many texts as a list does, each as long as a {@code String}. */
    @Test
    void copiesAndJoinsFitWhereTheTextsAndTheirSeamsDo() {
        fitsUpTo((L - 6) / 3, "String.repeat(3, v)");
        fitsUpTo((L - 6) / 3, "String.concat([v, v, v])");
        fitsUpTo((L - 7) / 2, "String.join(\",\", [v, v])");
        notShownReachedAtEveryValue(model(atMost(10), "String.concat(ns) ++ v"));
    }

    /**
     * A list of the input held to three texts and no shorter ones: each may be as long as a
     * {@code String}, so the join is not shown to fit however short {@code v} is. A rule on how
     * many the list holds bounds the texts it holds no further.
     */
    @Test
    void aJoinOfAListHeldToAFewTextsOfAnyLengthIsNotShownToFit() {
        String joined = """
                module held

                data V = String invariant String.length(value) <= %s
                data Ws = List<String> invariant List.length(value) <= 3

                behavior f : (v: V, ns: List<String>, ws: Ws) -> Bool
                let f (V(v), ns, Ws(ws)) = {
                    let m = String.join(",", ws) ++ v
                    List.any(own -> own == v, ns) || String.length(m) > 0
                }
                """;
        notShownReachedAtEveryValue(joined.formatted(10));
    }

    /** What a text built of texts is handed may itself be built, chosen or converted: each is as
     *  long as its own account says at most. */
    @Test
    void aTextBuiltOfBuiltTextsFitsWhereWhatItIsHandedDoes() {
        fitsUpTo((L - 6) / 3, "(v ++ v) ++ v");
        fitsUpTo((L - 3) / 2, "v ++ (if up then v else \"x\")");
        fitsUpTo((L - 4) / 4, "String.lowercase(v) ++ \"x\"");
    }

    /**
     * A reversal and a replacement are put in canonical form whole, which makes a text at most
     * four times as long: {@code 4n}, and with each code point replaced by two, {@code 8n}.
     */
    @Test
    void aTextPutInCanonicalFormWholeFitsWhereFourTimesItDoes() {
        fitsUpTo(L / 4, "String.reverse(v)");
        fitsUpTo(L / 8, "String.replace(\"a\", \"bb\", v)");
    }

    /**
     * Padding is of the width and the pad, and not of the text, which is answered as it is where
     * it is that wide already: a width of ten gets past whatever {@code v} is. The join is at most
     * four times seventeen times the width.
     */
    @Test
    void paddingFitsWhereTheWidthDoes() {
        reachedAtEveryValue(model("", "String.padLeft(10, \"0\", v)"));
        reachedAtEveryValue(model("", "String.padRight(" + L / 68 + ", \"0\", v)"));
        notShownReachedAtEveryValue(model("", "String.padRight(" + (L / 68 + 1) + ", \"0\", v)"));
    }
}
