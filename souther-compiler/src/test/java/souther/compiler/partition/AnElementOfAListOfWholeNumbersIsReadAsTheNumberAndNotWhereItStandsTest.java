package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * The element a walk hands its step over a list of every whole number between two is read as the
 * number it is, and not as where it stands: over {@code List.rangeInclusive(3, days)} the element
 * is three where it stands first. A line through it is drawn at that number, beside a run that
 * stops in the sum over it, as the same comparison over an element of a list of the input is.
 */
class AnElementOfAListOfWholeNumbersIsReadAsTheNumberAndNotWhereItStandsTest {

    /** {@code a + n >= 10} with {@code n} from three is at {@code a} of seven; read as where
     *  {@code n} stands, it would be at ten. */
    @Test
    void aLineThroughTheElementIsDrawnAtTheNumber() {
        assertEquals(List.of("7"), lines(compiled("a: Int, days: Int",
                "List.any(n -> a + n >= 10, List.rangeInclusive(3, days))")));
    }

    /** The same comparison over an element of a list of the input is a line on the form, a
     *  relation of the element to another value, and each of its sums a step a run that gets
     *  there stops at where the sum is past its type. What a walk stopping at an answer is made
     *  under is not read as relations, so each stop is said as not resolved, with the rows every
     *  run getting there stops at: those of the second are where it is past its type, said of
     *  the runs that get to it, which a run whose first sum is past its type does not. */
    @Test
    void theSameComparisonOverAnElementOfTheInputIsReadAsItWas() {
        List<String> report = report("a: Int, ns: List<Nat>",
                "List.any(v -> a + v + 3 >= 10, List.map(n -> n.value, ns))");
        assertEquals(List.of(
                "· no line: comparison@4:41 — it relates the value here to another value rather"
                        + " than dividing the values here, about `ns[*]`",
                "· stop not resolved: 4:33; whether a run stops in a + ns[*] is not determined: "
                        + A_CONDITION_NOT_READ + "; a run that gets there stops in a + ns[*] where"
                        + " a + ns[*] is at least 9223372036854775808, and it is not shown that"
                        + " any such run exists",
                "· stop not resolved: 4:37; whether a run stops in a + ns[*] + 3 is not"
                        + " determined: " + A_CONDITION_NOT_READ + "; a run that gets there stops"
                        + " in a + ns[*] + 3 where a + ns[*] is at least 9223372036854775805, and"
                        + " it is not shown that any such run exists"),
                report.stream().filter(line -> line.startsWith("· no line")
                        || line.startsWith("· may stop")
                        || line.startsWith("· stop not resolved")).toList());
        assertEquals(List.of("7", "0", "7"), lines(compiled("a: Int, ns: List<Nat>",
                "List.any(v -> a + v + 3 >= 10, List.map(n -> n.value, ns))")));
    }

    /**
     * A sum over where an element stands, past the type at some places and at none for every
     * place of a row, may stop some runs and no form of the input says which: it is a step whose
     * stop is not resolved, with no rows where every run does.
     */
    @Test
    void aSumPastItsTypeAtSomePlacesIsAStepWhoseStopIsNotResolved() {
        List<String> report = report("a: Nat, xs: List<Int>",
                "List.any(b -> b, List.mapIndexed((i, _) -> a.value + i >= 10, xs))");
        assertEquals(List.of("· stop not resolved: 4:68; whether a run stops in a + i is not"
                        + " determined: it is over a value the body works out, such as a total or"
                        + " a product, and not over numbers of the input"),
                report.stream().filter(line -> line.startsWith("· may stop")
                        || line.startsWith("· stop not resolved")).toList());
    }

    /**
     * A walk that does not stop on an answer makes every application, so the sum over the last
     * element stops a run where it is past the type, after the first got past; and each
     * application still draws its own line, the stop taking none away. The sum is worked out on
     * the application the second element is handed, which every run makes, the first having got
     * past: a value of the input shown to stop there is a run that does. What every run stops at
     * is not said of the step, which a run gets to on two applications, each proved in its own
     * names.
     */
    @Test
    void aSumOverTheLastElementAFilterIsHandedStopsEveryRunPastIt() {
        Compilation compilation = ACompiledModel.measured("""
                module w1
                behavior m : (a: Int) -> List<Int>
                let m (a) = List.filter(n -> n + a >= 0, [0, 10])
                """, Adequacy.Asked.fullReport());
        List<String> report = AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .map(String::strip).toList();
        assertEquals(List.of("· may stop a run: 3:32 — a run with a = 9223372036854775798 gets"
                        + " here and stops in a + 10"),
                report.stream().filter(line -> line.startsWith("· may stop")
                        || line.startsWith("· stop not resolved")).toList());
        assertEquals(List.of("0", "-10"), lines(compilation));
    }

    /** Why a stop worked out on an application is not resolved where what the application is
     *  made under is not read, as the report says it. */
    private static final String A_CONDITION_NOT_READ = "a condition on the way is not a comparison"
            + " of whole numbers of the input, so no input is checked against it";

    /** The values of the lines drawn in {@code m}, in the order they are measured. */
    private static List<String> lines(Compilation compilation) {
        List<BorderAssessment> lines = Adequacy.readingsOf(compilation.db(), "w1").get("m");
        assertNotNull(lines, "m was measured");
        return lines.stream().map(BorderAssessment::value).toList();
    }

    private static List<String> report(String parameters, String body) {
        Compilation compilation = compiled(parameters, body);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .map(String::strip).toList();
    }

    private static Compilation compiled(String parameters, String body) {
        return ACompiledModel.measured("""
                module w1
                data Nat = Int invariant value >= 0
                behavior m : (%s) -> Bool
                let m (%s) = %s
                """.formatted(parameters, parameters.replaceAll(":\\s*[A-Za-z<>]+", ""), body),
                Adequacy.Asked.fullReport());
    }
}
