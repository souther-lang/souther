package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecidingCase;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.WhereEachLineDecides;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * That the comparisons of a number make few ways of coming out together says nothing of how many
 * ways a reading of the cases is left with once the model is written with fewer of them, so a
 * report predicts no such count.
 *
 * <p>The model searches four candidates for the first whose number lies between one and five and
 * is not a given one. Written with the two bounds, the cases where its lines decide come to fewer
 * ways than written with the range as one comparison, or with the bounds taken as one part of the
 * statement: a part standing for the range ties no candidate to another, and an absolute value
 * chooses by cases of its own. What the numbers leave of the bounds — two points a candidate's
 * number is on one side of, so three ways — is true of all three, and is what a report says.
 */
class ARangeWrittenAsOnePartIsNotTakenApartIntoFewerWaysTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String BOUNDS = "x - k >= 1 && x - k <= 5";

    private static String model(String range) {
        return """
                module demo exposing (g)

                behavior g : (x: Int, h: Int) -> Bool
                let g (x, h) =
                    Option.withDefault(0 - 1, List.find(k -> RANGE && Bool.not(x + k == h),
                        [0, 1, 2, 3])) > 2
                """.replace("RANGE", range);
    }

    private static Compilation compiled(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.OFF));
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), source);
        return compilation;
    }

    /** The numbers of {@code g}'s input the model measures in whole numbers. */
    private static Predicate<NumericTerm> wholeNumbers(Compilation compilation) {
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("g");
        return inputs.reading(rules).quantities()::countsWhole;
    }

    /** What the body of {@code g} states, as the reading of it concludes. */
    private static Proposition stated(Compilation compilation) {
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        assertNotNull(checked, "the model compiles");
        AnalysisBody analysis = checked.analysisBodies().get("g");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("g");
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        return Pullback.ofATruth(Core.withoutStanding(analysis.core()), reads,
                inputs.reading(rules), Optional.empty()).proposition();
    }

    /** Every way of choosing a case where some line of {@code stated} decides, over its lines. */
    private static BigInteger waysOverEveryLine(Proposition stated,
                                                Predicate<NumericTerm> whole) {
        BigInteger out = BigInteger.ZERO;
        for (WhereEachLineDecides.Decides line : WhereEachLineDecides.in(stated, whole)) {
            for (DecidingCase one : line.cases()) {
                out = out.add(one.standsFor().structuralWays(BigInteger.TWO.pow(64)));
            }
        }
        return out;
    }

    /** A lower and an upper bound of one form, in one conjunction, taken as one part. */
    private static Proposition boundsAsOnePart(Proposition stated, int[] made) {
        if (stated instanceof Proposition.All all) {
            List<Proposition> parts = new ArrayList<>(all.parts().stream()
                    .map(each -> boundsAsOnePart(each, made)).toList());
            for (int at = 0; at < parts.size(); at++) {
                for (int other = at + 1; other < parts.size(); other++) {
                    if (side(parts.get(at)) * side(parts.get(other)) == -1
                            && formOf(parts.get(at)).equals(formOf(parts.get(other)))) {
                        parts.set(at, new Proposition.Truth(new DecisionSubject.AnInput(
                                TermPath.of("range" + made[0]++)), true));
                        parts.remove(other);
                        break;
                    }
                }
            }
            return Proposition.all(parts);
        }
        return stated instanceof Proposition.Any any ? Proposition.any(any.parts().stream()
                .map(each -> boundsAsOnePart(each, made)).toList()) : stated;
    }

    /** One for a lower bound of its form, minus one for an upper, nought for neither. */
    private static int side(Proposition part) {
        if (!(part instanceof Proposition.Compared(Relation.Affine affine, boolean holds, var _))) {
            return 0;
        }
        int side = switch (affine.proposition()) {
            case GE, GT -> 1;
            case LE, LT -> -1;
            case EQ, NE -> 0;
        };
        return holds ? side : -side;
    }

    private static Object formOf(Proposition part) {
        return ((Relation.Affine) ((Proposition.Compared) part).relation()).form().coefs();
    }

    /**
     * Observed with this compiler, and not a figure any reading owes: the cases are taken apart
     * into fewer ways written with the two bounds than either way of writing the range as one.
     * Should the taking apart change, the numbers here are what changes; the contract is below.
     */
    @Test
    void writtenWithTheTwoBoundsTheCasesComeToFewerWays() {
        Compilation written = compiled(model(BOUNDS));
        Proposition bounds = stated(written);
        BigInteger asWritten = waysOverEveryLine(bounds, wholeNumbers(written));
        BigInteger onePart = waysOverEveryLine(boundsAsOnePart(bounds, new int[1]),
                wholeNumbers(written));
        Compilation absolute = compiled(model("Int.abs(2 * (x - k) - 6) <= 4"));
        BigInteger oneComparison = waysOverEveryLine(stated(absolute), wholeNumbers(absolute));
        assertEquals(BigInteger.valueOf(162), asWritten);
        assertEquals(BigInteger.valueOf(740), onePart);
        assertEquals(BigInteger.valueOf(438), oneComparison);
        assertTrue(asWritten.compareTo(onePart) < 0 && asWritten.compareTo(oneComparison) < 0,
                "fewer comparisons, more ways: " + asWritten + ", " + onePart + ", "
                        + oneComparison);
    }

    /**
     * What a report says of a case is what the numbers leave and what made its parts, and never
     * a count a rewrite would leave: no field of an entry is one.
     */
    @Test
    void aReportSaysWhatTheNumbersLeaveAndPredictsNoCountAfterARewrite() {
        String model = """
                module demo exposing (g)

                behavior g : (x: Int, h: Int) -> Bool
                let g (x, h) =
                    Option.withDefault(0 - 1, List.find(k -> x - k >= 1 && x - k <= 5
                            && Bool.not(x + k == h), [0, 1, 2, 3, 4, 5, 6])) > 2
                """;
        JsonNode expansions = JSON.readTree(AdequacyReport.of(compiled(model))
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)))
                .path("modules").get(0).path("behaviors").get(0).path("partition")
                .path("caseExpansions");
        assertFalse(expansions.isEmpty(), "the search is past the figure");
        boolean bounded = false;
        for (JsonNode each : expansions) {
            assertFalse(each.path("readings").isEmpty(), "a case is read somewhere: " + each);
            for (JsonNode reading : each.path("readings")) {
                JsonNode said = reading.path("caseExpansion");
                Set<String> fields = new java.util.TreeSet<>();
                said.propertyNames().forEach(fields::add);
                assertEquals(Set.of("structuralWays", "numericallyConsistentWays",
                        "partsSplitOn", "unattributed", "factors", "diagnosed"), fields,
                        "the counts, what made the parts, and what the numbers leave: " + said);
                for (JsonNode diagnosis : said.path("diagnosed")) {
                    bounded |= diagnosis.path("kind").asString().equals("orderedBoundaries");
                }
            }
        }
        assertTrue(bounded, "the bounds of a candidate's number are diagnosed: " + expansions);
    }
}
