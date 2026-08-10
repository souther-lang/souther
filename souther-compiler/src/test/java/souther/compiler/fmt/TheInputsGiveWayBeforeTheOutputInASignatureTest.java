package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior signature that does not fit breaks its parameter list before its output union.
 *
 * <p>Written as the rule rather than as an output. The order used to be whichever of the two the
 * layout reached with too little room left, which is the parameter list last because it is written
 * first — an answer that came from how the document was built and would come out the other way
 * after a rearrangement no test would call a change. So what is asserted is the implication over a
 * swept family: a signature whose union is broken has its parameters broken too. One expected
 * string would hold just as well if the order had been arrived at by accident.
 *
 * <p>The width decides which of the three outcomes a signature gets, and the sweep is required to
 * produce all three. An implication holds vacuously over a family that never reaches its premise,
 * so a sweep of only-flat signatures would pass this having asked nothing.
 */
class TheInputsGiveWayBeforeTheOutputInASignatureTest {

    private static final int WIDTH = 100;

    /** One signature of the sweep, and what the canonical form did to it. */
    private record Laid(String source, String text, boolean inputsBroken, boolean outputBroken) {}

    @Test
    void anOutputIsNeverBrokenWhileTheInputsAreIntact() {
        List<String> wrong = new ArrayList<>();
        for (Laid laid : sweep()) {
            if (laid.outputBroken() && !laid.inputsBroken()) {
                wrong.add(laid.text());
            }
        }
        assertEquals(List.of(), wrong,
                wrong.size() + " signatures broke the output union with the parameter list left on"
                        + " one line, which is the order reversed:\n" + String.join("\n", wrong));
    }

    /** The premise is reached: the sweep holds a signature of each of the three outcomes, so the
     *  implication above is not answered by a family that never breaks anything. */
    @Test
    void theSweepReachesAllThreeOutcomes() {
        int flat = 0;
        int inputsOnly = 0;
        int both = 0;
        for (Laid laid : sweep()) {
            if (!laid.inputsBroken() && !laid.outputBroken()) {
                flat++;
            } else if (laid.inputsBroken() && !laid.outputBroken()) {
                inputsOnly++;
            } else if (laid.inputsBroken() && laid.outputBroken()) {
                both++;
            }
        }
        assertTrue(flat > 0 && inputsOnly > 0 && both > 0,
                "the sweep reached " + flat + " signatures written on one line, " + inputsOnly
                        + " with the inputs broken alone and " + both + " with both broken");
    }

    /** Nothing is broken that fits, and nothing that does not fit is left whole. The order says
     *  which of the two gives way; this says that one of them had to. */
    @Test
    void aSignatureBreaksWhenItDoesNotFitAndNotBefore() {
        List<String> wrong = new ArrayList<>();
        for (Laid laid : sweep()) {
            boolean fitsOnOneLine = oneLine(laid.source()).length() <= WIDTH;
            if (fitsOnOneLine && (laid.inputsBroken() || laid.outputBroken())) {
                wrong.add("broke a signature of " + oneLine(laid.source()).length()
                        + " columns:\n" + laid.text());
            }
            if (!fitsOnOneLine && !laid.inputsBroken()) {
                wrong.add("left a signature of " + oneLine(laid.source()).length()
                        + " columns on one line:\n" + laid.text());
            }
        }
        assertEquals(List.of(), wrong, String.join("\n", wrong));
    }

    /**
     * The union goes down the page only where the line the {@code )} leaves it on is too narrow for
     * it. That is the second half of the order: having given way at the inputs, the layout takes the
     * output only if it still has to.
     */
    @Test
    void anOutputIsBrokenOnlyWhereItDoesNotFitTheLineTheInputsLeftIt() {
        List<String> wrong = new ArrayList<>();
        for (Laid laid : sweep()) {
            if (!laid.inputsBroken()) {
                continue;
            }
            // `) -> ` and the union, which is the line the inputs left for the output.
            int columns = ") -> ".length() + unionOf(laid.source()).length();
            if (laid.outputBroken() != (columns > WIDTH)) {
                wrong.add("an output of " + columns + " columns came back "
                        + (laid.outputBroken() ? "broken" : "whole") + ":\n" + laid.text());
            }
        }
        assertEquals(List.of(), wrong, String.join("\n", wrong));
    }

    /** Every width from a signature that fits to one whose union alone does not, in both
     *  directions, so that the two are varied against each other rather than one at a time. */
    private static List<Laid> sweep() {
        List<Laid> out = new ArrayList<>();
        for (int params = 1; params <= 3; params++) {
            for (int nameLength : new int[] {3, 12, 30}) {
                for (int members = 1; members <= 3; members++) {
                    for (int memberLength : new int[] {6, 22, 40}) {
                        String source = signature(params, nameLength, members, memberLength);
                        String text = Formatter.format(source);
                        out.add(new Laid(source, text, inputsBroken(text), outputBroken(text)));
                    }
                }
            }
        }
        return out;
    }

    private static String signature(int params, int nameLength, int members, int memberLength) {
        StringBuilder sb = new StringBuilder("module m\n\nbehavior act : (");
        for (int i = 0; i < params; i++) {
            sb.append(i == 0 ? "" : ", ").append(name('a', nameLength, i)).append(": Int");
        }
        sb.append(") -> ");
        for (int i = 0; i < members; i++) {
            sb.append(i == 0 ? "" : " | ").append(name('A', memberLength, i));
        }
        return sb.append("\n").toString();
    }

    /** A name of exactly {@code length} characters, distinct per index. */
    private static String name(char first, int length, int index) {
        String tail = Integer.toString(index);
        return first + "x".repeat(length - 1 - tail.length()) + tail;
    }

    /** The signature as one line, which is the width the layout was asked about. */
    private static String oneLine(String source) {
        for (String line : source.split("\n", -1)) {
            if (line.startsWith("behavior ")) {
                return line;
            }
        }
        throw new IllegalStateException("no signature in " + source);
    }

    /** What the source writes after the arrow. */
    private static String unionOf(String source) {
        String line = oneLine(source);
        return line.substring(line.indexOf(") -> ") + ") -> ".length());
    }

    /** The parameter list is broken when the signature's own line ends at the {@code (}. */
    private static boolean inputsBroken(String text) {
        for (String line : text.split("\n", -1)) {
            if (line.matches("^behavior \\S+ : \\($")) {
                return true;
            }
        }
        return false;
    }

    /** The union is broken when a member opens a line with its {@code |}. */
    private static boolean outputBroken(String text) {
        for (String line : text.split("\n", -1)) {
            if (line.matches("^\\s+\\| \\S.*$")) {
                return true;
            }
        }
        return false;
    }
}
