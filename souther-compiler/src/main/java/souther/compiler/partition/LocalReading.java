package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.UnreadRule;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.values.AdmissibleSet;

import java.util.List;

/**
 * What reading a position's own type and rules comes to, whatever it found.
 *
 * <p>One value because it is one reading. These are not what the reading concluded — they are
 * what it saw on the way, and they are the same whether it came back with evidence or with nothing.
 * Held once, they cannot come to differ: copied into each answer, the day somebody works out
 * {@link #admissible} differently for a position that has classes is a day the compiler contradicts
 * itself about where the same values stop.
 *
 * @param term       which number the position is measured at: what it holds, or what its rules take
 *                   of it. Always one — a position is an axis's worth of something even where
 *                   nothing divides it, and the axis is named after this
 * @param admissible what every rule reaching the position leaves its values, or null where nothing
 *                   bounds them. Not where it is divided: a cap the record alone imposes stops the
 *                   values without drawing a line through them
 * @param admitted   which values the position may hold, with how much of what its rules say was
 *                   read. A separate question from {@link #admissible} and not a second answer to
 *                   it: a rule can name the values a position holds without stating where they
 *                   stop, and one can state where they stop without naming any
 * @param unread     the rules written here that this could not turn into an end. A fact about those
 *                   rules and not about the position, which is why it travels beside the answer
 *                   rather than in it
 */
public record LocalReading(NumericTerm term, NumericDomain.Bounds admissible,
                           AdmissibleSet admitted, List<UnreadRule> unread) {

    public LocalReading {
        unread = List.copyOf(unread);
    }
}
