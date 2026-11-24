package souther.compiler.numeric;

import souther.compiler.numeric.RulesAsWritten.Written;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import static souther.compiler.numeric.RulesAsWritten.rule;

/**
 * Rules that are bounds on the sums of one growing prefix of positions, drawn at random, for the
 * tests that hold what is left of such rules to the whole-numbered points that satisfy them.
 *
 * <p>Each position is boxed within {@link #REACH}, so no solution is left out of the points over
 * that range, and each prefix of two positions or more has at least one bound, so the rules are a
 * chain a basis is chosen for.
 */
final class PrefixChains {

    static final List<String> ATOMS = List.of("a", "b", "c", "d");
    static final int REACH = 5;

    private static final List<String> RELATIONS = List.of("<=", "<", ">=", ">");

    private PrefixChains() {
    }

    /** A chain over the first {@code positions} of {@link #ATOMS}. */
    static List<Written> chain(Random random, int positions) {
        List<String> atoms = ATOMS.subList(0, positions);
        List<Written> out = new ArrayList<>();
        for (String atom : atoms) {
            out.add(rule(atom + " >= " + (-REACH + random.nextInt(4))));
            out.add(rule(atom + " <= " + (REACH - random.nextInt(4))));
        }
        StringBuilder prefix = new StringBuilder(atoms.getFirst());
        for (int at = 1; at < atoms.size(); at++) {
            prefix.append(" + ").append(atoms.get(at));
            boolean bounded = false;
            for (String relation : RELATIONS) {
                if (random.nextInt(4) == 0) {
                    out.add(rule(prefix + " " + relation + " " + (random.nextInt(15) - 7)));
                    bounded = true;
                }
            }
            if (!bounded) {
                out.add(rule(prefix + " " + RELATIONS.get(random.nextInt(4)) + " "
                        + (random.nextInt(15) - 7)));
            }
        }
        return out;
    }
}
