package souther.compiler;

import java.util.ArrayList;
import java.util.List;

/**
 * A value's spelling with every set in it said in one order, for comparing two spellings of a model
 * whose cases were renamed.
 *
 * <p>A set of cases is spelled in the order its names compare in, which is the one order a set can
 * be spelled in by itself — so renaming the cases of a model can spell one set two ways, and a test
 * putting the names back and comparing the text would read that as two values. What it compares is
 * the values, so the sets are put in one order after the names are put back.
 *
 * <p>The sets are the ones a value of this compiler spells as sets: the cases a narrowing leaves
 * ({@code CasesLeft[...]}) and the answers a fork has ({@code answers=[...]}).
 */
final class SpelledSets {

    private static final List<String> OPENINGS = List.of("answers=[", "CasesLeft[");

    private SpelledSets() {
    }

    /** {@code said} with the members of every set in it in one order. */
    static String inOneOrder(String said) {
        StringBuilder out = new StringBuilder();
        int from = 0;
        while (true) {
            int at = -1;
            String opening = null;
            for (String each : OPENINGS) {
                int found = said.indexOf(each, from);
                if (found >= 0 && (at < 0 || found < at)) {
                    at = found;
                    opening = each;
                }
            }
            if (at < 0) {
                out.append(said, from, said.length());
                return out.toString();
            }
            int open = at + opening.length();
            int close = closing(said, open);
            out.append(said, from, open);
            List<String> members = new ArrayList<>();
            for (String member : membersOf(said.substring(open, close))) {
                members.add(inOneOrder(member));
            }
            members.sort(null);
            out.append(String.join(", ", members)).append(']');
            from = close + 1;
        }
    }

    /** Where the bracket opened just before {@code from} closes. */
    private static int closing(String said, int from) {
        int depth = 1;
        for (int at = from; at < said.length(); at++) {
            char each = said.charAt(at);
            if (each == '[' || each == '{') {
                depth++;
            } else if (each == ']' || each == '}') {
                depth--;
                if (depth == 0) {
                    return at;
                }
            }
        }
        throw new IllegalArgumentException("a set that does not close: " + said);
    }

    /** The members of a set's inside, split where no bracket is open. */
    private static List<String> membersOf(String inside) {
        List<String> out = new ArrayList<>();
        int depth = 0;
        int start = 0;
        for (int at = 0; at < inside.length(); at++) {
            char each = inside.charAt(at);
            if (each == '[' || each == '{') {
                depth++;
            } else if (each == ']' || each == '}') {
                depth--;
            } else if (depth == 0 && inside.startsWith(", ", at)) {
                out.add(inside.substring(start, at));
                start = at + 2;
            }
        }
        if (start < inside.length()) {
            out.add(inside.substring(start));
        }
        return out;
    }
}
