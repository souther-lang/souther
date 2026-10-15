package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.DecisionRule;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many of the candidates written out every clue lets stand, held against one, is a decision
 * over which case each clue names, and no line on the order the candidates are declared in.
 *
 * <p>{@code length(filter(w -> all(c -> holds(c, w), cs), suspects)) == 1} counts statements, one
 * per candidate written out, each of which asks of every clue which case it names. Exactly one
 * holding is one of the ways those statements can come out together, so what the fork owes is its
 * two sides, and no row beside a candidate declared next to another: {@code Ben} is no nearer to
 * {@code Ann} than {@code Cat} is.
 */
class HowManyCandidatesFitIsADecisionOverTheCasesTest {

    /** Three candidates. */
    private static final List<String> THREE = List.of("Ann", "Ben", "Cat");

    /** The rows: none fits, one fits, and two do. */
    private static final String ROWS = """

            example f
                | "none fits" : ([ Did { who = FIRST }, Did { who = SECOND } ]) -> NoneFits
                | "one named" : ([ Did { who = FIRST } ]) -> One
                | "FIRST cleared" : ([ Clear { who = FIRST } ]) -> ANSWER
            """;

    private static String source(List<String> declared, List<String> candidates, String answer) {
        return model(declared, candidates)
                + ROWS.replace("FIRST", candidates.get(0)).replace("SECOND", candidates.get(1))
                .replace("ANSWER", answer);
    }

    /** The model and no row of it. */
    private static String model(List<String> declared, List<String> candidates) {
        String each = String.join(" | ", declared);
        String all = String.join(", ", candidates);
        return """
                module probe.clues

                import List ( filter, all, get, length )

                data Who = CANDIDATES
                data Did = { who: Who }
                data Clear = { who: Who }
                data Clue = Did | Clear
                data One
                data NotOne
                data NoneFits

                let suspects = [ SUSPECTS ]

                let holds (c: Clue, w: Who): Bool =
                    match c with
                        | Did { who }   -> w == who
                        | Clear { who } -> w /= who

                behavior f : (cs: List<Clue>) -> One | NotOne | NoneFits

                let f (cs) = {
                    let fitting = filter(w -> all(c -> holds(c, w), cs), suspects)
                    match get(0, fitting) with
                        | None   -> NoneFits
                        | Some w -> if length(fitting) == 1 then One else NotOne
                }
                """.replace("CANDIDATES", each).replace("SUSPECTS", all);
    }

    /** With three candidates, clearing one leaves two. */
    private static String three(List<String> declared) {
        return source(declared, THREE, "NotOne");
    }

    @Test
    void noneOneAndTwoFittingAreTheThreeAnswers() {
        Compilation compilation = measured(three(THREE));
        assertEquals(List.of(), errorsOf(compilation),
                "none fitting is NoneFits, one is One, and two are NotOne");
        assertFalse(errorsOf(measured(source(THREE, THREE, "One"))).isEmpty(),
                "control: two fitting is not One, and a row saying so does not hold");
    }

    @Test
    void theForkIsOwedBothSidesAndNoLine() {
        Compilation compilation = measured(three(THREE));
        String report = report(compilation);
        assertTrue(headed(report, "border").contains("not applicable"), report);
        assertTrue(headed(report, "decision").contains("rules 3   taken 3"),
                () -> "no fit, one fit and more than one are the three ways: " + report);
    }

    /** Which case is declared beside which says nothing of how many fit. */
    @Test
    void reorderingTheCandidatesChangesNothingOwed() {
        Compilation declared = measured(three(THREE));
        Compilation reordered = measured(three(List.of("Cat", "Ann", "Ben")));
        assertEquals(List.of(), errorsOf(reordered));
        for (String section : List.of("border", "decision", "combination", "partition")) {
            assertEquals(headed(report(declared), section), headed(report(reordered), section),
                    section);
        }
        assertEquals(owed(declared), owed(reordered));
    }

    /** Past more candidates than a way is looked along one at a time, the fork is read the same. */
    @Test
    void pastTheFigureTheForkIsStillADecisionOverTheCases() {
        List<String> many = IntStream
                .rangeClosed(0, CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum())
                .mapToObj(each -> "W" + each).toList();
        Compilation compilation = measured(source(many, many, "NotOne"));
        assertEquals(List.of(), errorsOf(compilation));
        String report = report(compilation);
        assertTrue(headed(report, "border").contains("not applicable"), report);
        assertTrue(headed(report, "decision").contains("rules 3   taken 3"), report);
    }

    /**
     * With no row written, a row is composed for each way of the fork — none fits, one does, more
     * than one do — past more candidates than a way is looked along one at a time as well.
     */
    @Test
    void aRowIsComposedForEachWayOfTheFork() {
        List<String> many = IntStream
                .rangeClosed(0, CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG.maximum())
                .mapToObj(each -> "W" + each).toList();
        for (List<String> candidates : List.of(THREE, many)) {
            Compilation compilation = measured(model(candidates, candidates));
            Map<DecisionRule, SettledAcross> searched = compilation.db()
                    .ask(new Adequacy.DecisionSearch("probe.clues", "f")).value();
            assertEquals(3, searched.size(), () -> "each way is searched: " + searched);
            searched.forEach((rule, settled) -> assertInstanceOf(RuleRequirement.Required.class,
                    settled.requirement(),
                    () -> "a row is composed and seen taking " + rule + " among "
                            + candidates.size() + " candidates"));
        }
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static List<String> errorsOf(Compilation compilation) {
        return compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList();
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** The line of the report that heads {@code section}. */
    private static String headed(String report, String section) {
        return report.lines().filter(line -> line.strip().startsWith(section + " "))
                .findFirst().orElse("no " + section + " in " + report);
    }

    /** Every combination owed, as the two classes it is of. */
    private static Set<String> owed(Compilation compilation) {
        PartitionEvidence evidence = compilation.db()
                .ask(new Adequacy.Coverage("probe.clues")).value().get("f");
        Set<String> out = new LinkedHashSet<>();
        for (PartitionEvidence.PairSpace.AxisPair pair : evidence.pairs().space()) {
            if (pair.owed() instanceof PartitionEvidence.PairSpace.Owed.Listed listed) {
                for (PartitionEvidence.PairSpace.Cell cell : listed.cells()) {
                    out.add(pair.between() + " " + cell.one() + " × " + cell.other());
                }
            }
        }
        return out;
    }
}
