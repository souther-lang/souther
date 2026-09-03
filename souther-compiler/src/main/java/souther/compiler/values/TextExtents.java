package souther.compiler.values;

import souther.compiler.numeric.Text;
import souther.compiler.regex.Language;
import souther.compiler.regex.Meter;
import souther.compiler.regex.PatternPlan;

/**
 * Where a language stops on the order the strings it holds are measured on.
 *
 * <p>The one place a set of strings and the order a position's values are counted on are brought
 * together. A {@link Language} is its strings and knows nothing about positions; {@link Text} is
 * where a string sits on the carrier's order and holds one string at a time. What a rule leaves a
 * position between is a question about both, and answering it anywhere else would be answering it
 * with whichever half was to hand.
 *
 * <p><b>Apart from {@link Sets}, which is the algebra of two sets.</b> This takes one and asks
 * something about the order — a different question, and the one that costs machines nobody else
 * needs. Written there, a caller meeting two sets would be holding an operation that projects.
 *
 * <p><b>What a run is established by.</b> A language is a run when the strings above its least that
 * it does not admit are everything from some string upwards. That is asked of the languages
 * themselves — the ones above a string, the ones this does not hold, and whether two of them are
 * one set — so nothing here decides what "between" means a second time. Convexity is not a word
 * used or wanted: a language that is not one run is one whichever way it fails to be, and a reading
 * that answered with the reason would be answering about the shape rather than about the edge.
 *
 * <p><b>All of it or none of it.</b> A reading stopped part way answers {@link
 * TextExtent.NotBuilt}, and never with the end it had reached. Half an answer would put a line on a
 * position when the machine for the other half happened to be affordable, which makes what a report
 * says about a model turn on what this compiler could build that day.
 */
public final class TextExtents {

    /**
     * Where {@code language} begins and ends, or why it names no run.
     *
     * <p>Its own allowance, spent whole here: what this asks for is machines nothing else wants,
     * and a caller with several rules pays for each of them on its own so that one expensive rule
     * does not take the line another rule drew.
     */
    public static TextExtent of(Language language) {
        return of(language, PatternPlan.Budget.OF_AN_ORDERED_EXTENT.meter());
    }

    /**
     * The same under a meter handed in, for a reader here that wants to see what running out comes
     * to.
     *
     * <p>Not the way in. A meter carries which limit refused the last thing built out of it, so one
     * that has been spent on something else answers this reading with a reason belonging to that —
     * which is why what a caller outside gets is the one above, with an allowance of its own.
     */
    static TextExtent of(Language language, Meter meter) {
        String first = language.least();
        if (first == null) {
            // Either it holds nothing, or its strings descend without stopping and what is below
            // all of them is not a string. Neither is a run with a string at its lower end, which
            // is what is being asked for, and neither is a limit of this compiler.
            return new TextExtent.NoNamedRun();
        }
        Language strings = Language.everyString(meter);
        Language above = strings == null ? null : notBefore(first, strings, meter);
        Language outside = above == null ? null : strings.and(language.not(meter), meter);
        // What the language leaves out from its least string upwards. Where that is nothing, the
        // language is everything from the least upwards; where it is everything from some string
        // upwards, the language is what lies between the two.
        Language left = outside == null ? null : above.and(outside, meter);
        if (left == null) {
            return new TextExtent.NotBuilt(stopped(meter));
        }
        if (left.isEmpty()) {
            return new TextExtent.One(Text.of(first), null);
        }
        String after = left.least();
        if (after == null) {
            return new TextExtent.NoNamedRun();
        }
        Language beyond = notBefore(after, strings, meter);
        if (beyond == null) {
            return new TextExtent.NotBuilt(stopped(meter));
        }
        return beyond.equals(left)
                ? new TextExtent.One(Text.of(first), Text.of(after))
                : new TextExtent.NoNamedRun();
    }

    /**
     * Every string from {@code from} upwards, or null past what {@code meter} allows.
     *
     * <p>Met with the strings, because what is wanted is a set two of these can be compared as. A
     * complement holds every sequence of symbols the machine does not stop on, and some of those are
     * sequences no string is read as — kept, two answers holding the same strings would compare
     * unequal, and a rule that names a run would be read as naming none.
     */
    private static Language notBefore(String from, Language strings, Meter meter) {
        Language before = Language.before(from, meter);
        Language above = before == null ? null : before.not(meter);
        return above == null ? null : strings.and(above, meter);
    }

    /**
     * Which limit refused the machine that did not come back.
     *
     * <p>Read off the meter rather than guessed at: a language larger than one machine may be is one
     * an author wrote and can write differently, and a build that had already spent this answer's
     * allowance is not. A meter that came back with nothing and names no limit is this compiler
     * having lost the reason on the way, which is a mistake here and not a model anybody can write.
     */
    private static Meter.Stopped stopped(Meter meter) {
        Meter.Stopped why = meter.stoppedBy();
        if (why == null) {
            throw new IllegalStateException(
                    "a machine was not built and the allowance refused nothing");
        }
        return why;
    }

    private TextExtents() {}
}
