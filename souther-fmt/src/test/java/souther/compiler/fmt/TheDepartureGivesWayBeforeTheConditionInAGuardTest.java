package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@code guard} that does not fit gives way at its {@code else} before it gives way in its
 * condition.
 *
 * <p>The departure is what the guard is for. Written wherever the condition happened to finish, it
 * ends up at the end of whichever continuation line the last conjunct took and reads as part of that
 * conjunct — which is what came out while the {@code else} was written with a boundary the layout
 * could not break at all, so nothing had decided the order and nothing could have said what it was.
 *
 * <p>Written as the rule and not as an output, the same way
 * {@link TheInputsGiveWayBeforeTheOutputInASignatureTest} is: over a swept family, a guard whose
 * condition is broken has its departure broken too, and the sweep is required to reach all three
 * outcomes so the implication is not answered by a family that never breaks anything.
 *
 * <p>A guard whose departures are named clauses is not this question. Its {@code else} already ends
 * the guard's own line with the clauses under it, so there is no order between two things to state.
 */
class TheDepartureGivesWayBeforeTheConditionInAGuardTest {

    private static final int WIDTH = 100;

    private record Laid(String source, String text, boolean departureBroken,
            boolean conditionBroken) {}

    @Test
    void aConditionIsNeverBrokenWhileTheDepartureIsStillOnTheGuardsLine() {
        List<String> wrong = new ArrayList<>();
        for (Laid laid : sweep()) {
            if (laid.conditionBroken() && !laid.departureBroken()) {
                wrong.add(laid.text());
            }
        }
        assertEquals(List.of(), wrong,
                wrong.size() + " guards broke the condition with the departure left on the guard's"
                        + " line, which is the order reversed:\n" + String.join("\n", wrong));
    }

    /** The premise is reached: the sweep holds a guard of each of the three outcomes. */
    @Test
    void theSweepReachesAllThreeOutcomes() {
        int flat = 0;
        int departureOnly = 0;
        int both = 0;
        for (Laid laid : sweep()) {
            if (!laid.departureBroken() && !laid.conditionBroken()) {
                flat++;
            } else if (laid.departureBroken() && !laid.conditionBroken()) {
                departureOnly++;
            } else if (laid.departureBroken() && laid.conditionBroken()) {
                both++;
            }
        }
        assertTrue(flat > 0 && departureOnly > 0 && both > 0,
                "the sweep reached " + flat + " guards on one line, " + departureOnly
                        + " with the departure broken alone and " + both + " with both broken");
    }

    /** Nothing is broken that fits, and nothing that does not fit is left whole. */
    @Test
    void aGuardBreaksWhenItDoesNotFitAndNotBefore() {
        List<String> wrong = new ArrayList<>();
        for (Laid laid : sweep()) {
            boolean fits = guardLine(laid.source()).length() <= WIDTH;
            if (fits && (laid.departureBroken() || laid.conditionBroken())) {
                wrong.add("broke a guard of " + guardLine(laid.source()).length() + " columns:\n"
                        + laid.text());
            }
            if (!fits && !laid.departureBroken()) {
                wrong.add("left a guard of " + guardLine(laid.source()).length()
                        + " columns on one line:\n" + laid.text());
            }
        }
        assertEquals(List.of(), wrong, String.join("\n", wrong));
    }

    /**
     * The condition goes down the page only where it does not fit the line the {@code guard} left
     * it, which is the second half of the order.
     */
    @Test
    void aConditionIsBrokenOnlyWhereItDoesNotFitTheLineTheGuardLeftIt() {
        List<String> wrong = new ArrayList<>();
        for (Laid laid : sweep()) {
            if (!laid.departureBroken()) {
                continue;
            }
            int columns = "    guard ".length() + conditionOf(laid.source()).length();
            if (laid.conditionBroken() != (columns > WIDTH)) {
                wrong.add("a condition of " + columns + " columns came back "
                        + (laid.conditionBroken() ? "broken" : "whole") + ":\n" + laid.text());
            }
        }
        assertEquals(List.of(), wrong, String.join("\n", wrong));
    }

    /** A guard whose departures are named clauses keeps the shape it already had. */
    @Test
    void namedDeparturesAreWrittenUnderTheGuardsOwnLine() {
        assertEquals("""
                module m

                data Lines = List<Int>
                    invariant nonEmpty = List.length(value) >= 1
                    invariant unique = List.allDistinctBy(x -> x, value)
                data Small = Int

                let build (rows) = {
                    guard Lines(rows) as items else
                        | nonEmpty -> Small(1)
                        | unique -> Small(2)
                    items
                }
                """, Formatter.format("""
                module m
                data Lines = List<Int>
                    invariant nonEmpty = List.length(value) >= 1
                    invariant unique = List.allDistinctBy(x -> x, value)
                data Small = Int

                let build (rows) = {
                    guard Lines(rows) as items else
                        | nonEmpty -> Small(1)
                        | unique -> Small(2)
                    items
                }
                """));
    }

    /** Both widths are varied against each other rather than one at a time. */
    private static List<Laid> sweep() {
        List<Laid> out = new ArrayList<>();
        for (int conjuncts = 1; conjuncts <= 3; conjuncts++) {
            for (int conjunctLength : new int[] {8, 24, 44}) {
                for (int departureLength : new int[] {5, 20, 40}) {
                    String source = guard(conjuncts, conjunctLength, departureLength);
                    String text = Formatter.format(source);
                    out.add(new Laid(source, text, departureBroken(text), conditionBroken(text)));
                }
            }
        }
        return out;
    }

    private static String guard(int conjuncts, int conjunctLength, int departureLength) {
        StringBuilder sb = new StringBuilder("module m\n\nlet f (n) = {\n    guard ");
        for (int i = 0; i < conjuncts; i++) {
            sb.append(i == 0 ? "" : " && ").append(name('c', conjunctLength, i)).append("(n)");
        }
        sb.append(" else ").append(name('D', departureLength, 0)).append("(n)");
        return sb.append("\n    n\n}\n").toString();
    }

    /** A name of exactly {@code length} characters, distinct per index. */
    private static String name(char first, int length, int index) {
        String tail = Integer.toString(index);
        return first + "x".repeat(length - 1 - tail.length()) + tail;
    }

    /** The guard as one line, which is the width the layout was asked about. */
    private static String guardLine(String source) {
        for (String line : source.split("\n", -1)) {
            if (line.strip().startsWith("guard ")) {
                return line;
            }
        }
        throw new IllegalStateException("no guard in " + source);
    }

    /** What the source writes between `guard` and `else`. */
    private static String conditionOf(String source) {
        String line = guardLine(source).strip();
        return line.substring("guard ".length(), line.lastIndexOf(" else "));
    }

    /** The departure is broken off when the `else` opens a line. */
    private static boolean departureBroken(String text) {
        for (String line : text.split("\n", -1)) {
            if (line.matches("^\\s+else \\S.*$")) {
                return true;
            }
        }
        return false;
    }

    /** The condition is broken when a conjunct opens a line with its operator. */
    private static boolean conditionBroken(String text) {
        for (String line : text.split("\n", -1)) {
            if (line.matches("^\\s+&& \\S.*$")) {
                return true;
            }
        }
        return false;
    }
}
