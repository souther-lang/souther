package souther.compiler.partition;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A rule cutting a position where no carrier counts is answered for, wherever the cut can stand.
 *
 * <p>A quotient puts a fraction where a rule compares, and a third is no value of either carrier.
 * What the geometry does with such a line is decline it — the border is there and no row is owed at
 * it — and declining is an answer a reader gets. Reaching one as a premise instead, the compile of a
 * model nothing is wrong with ends where the level was asked for a place it is not.
 *
 * <p><b>Over the roles a number can be in, and not over the one that was found.</b> A line lands in
 * a rule at the threshold, inside a coefficient, on either side of a comparison, and on a quantity
 * whose own lattice it makes fractional; both carriers hold it, and every operator an author can
 * write reaches it by a different arm. The shapes are crossed rather than sampled, because which of
 * them a level survives is what this is about — held on one, a reading that answered for the
 * threshold alone would pass.
 *
 * <p><b>One module and not one apiece.</b> What is being asked of each rule is what the report says
 * about the behavior it is written in, and a behavior is where a report is keyed — so every rule in
 * the sweep stands in one source, and the whole crossing is compiled once. Which rule stopped the
 * reading is the question that wants them apart, and it is asked only where one did
 * ({@link #whichOneStopped}): a run that answers for all of them has nothing to tell apart.
 *
 * <p><b>And what is asked for is the report and not the absence of a throw.</b> A harness that
 * compiled nothing would see no throw either, so one rule here is held to drawing a line: it is
 * the same crossing under a claim that cannot be met by falling silent.
 */
class ALineAtANumberNoCarrierCountsToIsAnsweredForTest {

    /**
     * A rule written with an operator put in, and how nought on its left side stands against its
     * right side where every position is at nought: below it, equal to it, or above it. That is
     * what decides the answer the one example of the behavior states.
     */
    private record Shape(String text, int noughtAgainstTheRight) {

        /** What the behavior answers with every position at nought, under {@code operator}. */
        String answerAtNought(String operator) {
            boolean holds = switch (operator) {
                case "<" -> noughtAgainstTheRight < 0;
                case "<=" -> noughtAgainstTheRight <= 0;
                case ">" -> noughtAgainstTheRight > 0;
                case ">=" -> noughtAgainstTheRight >= 0;
                default -> noughtAgainstTheRight == 0;
            };
            return holds ? "Yes { v = 1 }" : "No { why = 0 }";
        }
    }

    /** The rules over one position, each written with an operator put in. */
    private static final List<Shape> ONE_POSITION = List.of(
            new Shape("n %s 1 / 3", -1),
            new Shape("n %s 2 / 3", -1),
            new Shape("n %s 1 / 7", -1),
            new Shape("n %s -1 / 3", 1),
            new Shape("1 / 3 * n %s 2", -1),
            new Shape("n / 3 %s 2", -1),
            new Shape("n / 3 %s 1 / 3", -1));

    /** And over two, where a third is a coefficient and where it is on both sides at once. */
    private static final List<Shape> TWO_POSITIONS = List.of(
            new Shape("m %s -1 / 3 * n + 30", -1),
            new Shape("m / 3 %s n / 3", 0),
            new Shape("n / 3 + m / 6 %s 1 / 2", -1));

    /** What each behavior of the crossing answers with every position at nought, by name. */
    private static final Map<String, String> ANSWERED_AT_NOUGHT = new LinkedHashMap<>();

    /** Every operator a rule over two numbers can be written with. The disequality is not one this
     *  language writes, so it is not one an author reaches a line at a third by. */
    private static final List<String> OPERATORS = List.of("<", "<=", ">", ">=", "==");

    /** The rule each behavior of the crossing is written with, by the name it is written under. */
    private static final Map<String, String> CROSSING = crossing();

    private static Map<String, String> crossing() {
        Map<String, String> out = new LinkedHashMap<>();
        int at = 0;
        for (String type : List.of("Int", "Decimal")) {
            for (String operator : OPERATORS) {
                for (Shape shape : ONE_POSITION) {
                    String named = "b" + at++ + " " + type;
                    out.put(named, shape.text().formatted(operator));
                    ANSWERED_AT_NOUGHT.put(named, shape.answerAtNought(operator));
                }
                for (Shape shape : TWO_POSITIONS) {
                    String named = "b" + at++ + " " + type;
                    out.put(named, shape.text().formatted(operator));
                    ANSWERED_AT_NOUGHT.put(named, shape.answerAtNought(operator));
                }
            }
        }
        return out;
    }

    /**
     * Every one of them is answered for.
     *
     * <p>Counted rather than asserted one at a time: what a reader needs is every rule this could
     * not answer for, and a run that stopped at the first of them says one rule and leaves the
     * crossing it was standing for unmeasured.
     */
    @Test
    void everyRuleCuttingAPositionAtSuchANumberIsAnsweredFor() {
        assertEquals(List.of(), whichOneStopped());
        assertEquals(2 * OPERATORS.size() * (ONE_POSITION.size() + TWO_POSITIONS.size()),
                CROSSING.size(), "every shape was crossed with every operator on both carriers");
    }

    /**
     * And the crossing is one a silent reading could not pass.
     *
     * <p>The measurement beside the sweep. A third on a whole-numbered position parts it between two
     * whole numbers, which is a line with points either side — so a harness that answered for every
     * rule by compiling none of them fails here.
     */
    @Test
    void andARuleInItDrawsALine() {
        PartitionEvidence read = whole().get(named("n > 1 / 3", "Int"));

        assertFalse(read.axes().isEmpty(), "a third parts the whole numbers");
        assertFalse(read.axes().getFirst().classes().isEmpty(),
                "and the position it parts has the classes it was parted into");
    }

    /** The name the crossing writes one of its rules under. */
    private static String named(String guard, String type) {
        return CROSSING.entrySet().stream()
                .filter(each -> each.getValue().equals(guard) && each.getKey().endsWith(type))
                .map(each -> each.getKey().split(" ")[0]).findFirst().orElseThrow();
    }

    /**
     * Which rules of the crossing the report could not be asked for, and what stopped each.
     *
     * <p>Asked of the whole crossing first, which is one compilation and one report. Where that
     * answers, every rule in it was answered for and there is nothing to tell apart; where it does
     * not, each rule is put on its own so that what comes back names the rule rather than the
     * crossing it was standing in.
     */
    private static List<String> whichOneStopped() {
        try {
            whole();
            return List.of();
        } catch (RuntimeException _) {
            List<String> stopped = new ArrayList<>();
            CROSSING.forEach((name, guard) -> {
                try {
                    divided(behaviors(Map.of(name, guard)));
                } catch (RuntimeException e) {
                    stopped.add(name + " — " + guard + " — " + e);
                }
            });
            return stopped;
        }
    }

    /**
     * The module read into the classes its rules divide its positions into.
     *
     * <p>Which is the reading this is about: what a line at such a number costs a reader is paid
     * where the rules are turned into classes, and the rows a search would then write at the points
     * of each are a further question with an answer of its own. Asked for the rows as well, the
     * sweep would spend the search on a hundred rules to reach a step every one of them takes
     * before it.
     */
    private static Map<String, PartitionEvidence> divided(String source) {
        Compilation compilation = ACompiledModel.answered(source);
        return compilation.db().ask(new Adequacy.Coverage("example.form")).value();
    }

    /** The whole crossing, divided once. Read when a question asks rather than in an initialiser,
     *  so a source that stopped compiling fails the reading that met it. */
    private static Map<String, PartitionEvidence> whole() {
        if (whole == null) {
            whole = divided(behaviors(CROSSING));
        }
        return whole;
    }

    private static Map<String, PartitionEvidence> whole;

    /** Let go at the end, so the fork's later classes do not carry this crossing's answers. */
    @AfterAll
    static void release() {
        whole = null;
    }

    /** One module holding a behavior per rule, each named by the crossing. */
    private static String behaviors(Map<String, String> rules) {
        StringBuilder out = new StringBuilder("""
                module example.form

                data No = { why: Int }
                data Yes = { v: Int }
                data Result = No | Yes
                """);
        rules.forEach((named, guard) -> {
            String[] parts = named.split(" ");
            String name = parts[0];
            String type = parts[1];
            boolean two = guard.contains("m");
            String value = type.equals("Int") ? "0" : "0m";
            String written = type.equals("Int") ? guard : guard.replaceAll("(\\d+)", "$1m");
            out.append("""

                    behavior %s : (%s) -> Result
                        constructs Yes, No
                    let %s (%s) = {
                        guard %s else No { why = 0 }
                        Yes { v = 1 }
                    }
                    example %s
                        | "one" : (%s) -> %s
                    """.formatted(name,
                    two ? "n: " + type + ", m: " + type : "n: " + type,
                    name, two ? "n, m" : "n",
                    written, name, two ? value + ", " + value : value,
                    ANSWERED_AT_NOUGHT.get(named)));
        });
        return out.toString();
    }
}
