package souther.compiler.values;

import souther.compiler.numeric.Text;
import souther.compiler.regex.Meter;

/**
 * Where the strings one rule admits begin and end on the order they are measured on, or why that
 * has no answer.
 *
 * <p>Asked of a language and of nothing else. Whether a rule was read at all, and which position it
 * is about, are settled before this and travel beside it — a rule whose pattern nothing worked out
 * never reaches here, so no arm below stands for one.
 *
 * <p><b>Three answers about three different things.</b> {@link One} is what the model says. {@link
 * NoNamedRun} is what this reading established about a language it had: the strings it admits are
 * not one stretch of the order with a string at either end. {@link NotBuilt} is about this compiler
 * and says nothing about the model. Folded into one "no edge", a rule an author can rewrite and a
 * limit they cannot see would read alike, and the second is the one a report has to name
 * ({@code UnreadReason}).
 */
public sealed interface TextExtent {

    /**
     * The strings run from {@code first} up to {@code after}, or from {@code first} without end.
     *
     * <p>The lower end is one of them and the upper is not, and there is no other shape. A run of
     * the strings begins at its least — which is a string, or there would be no run named here —
     * and a string just below another is a thing this order does not have, so an upper end that
     * were one of them would have to be the greatest string admitted and there is none. Written as
     * a pair of endpoints either of which could be open, the shapes nothing can mean would be
     * spellable.
     *
     * @param first the least string the rule admits, which it admits
     * @param after the least string above every one it admits, which it does not admit, or null
     *              where there is no such string and the run has no end
     */
    record One(Text first, Text after) implements TextExtent {

        public One {
            if (first == null) {
                throw new IllegalArgumentException("a run begins at a string");
            }
            if (after != null && after.compareTo(first) <= 0) {
                throw new IllegalArgumentException(
                        "a run ends above where it begins: " + first + " up to " + after);
            }
        }

        /**
         * Whether the run holds one string and no other.
         *
         * <p>Asked of the order and not of the language: a run ends where the next string above its
         * first one begins exactly when there is nothing between them, and what is just above a
         * string is the order's answer ({@link Text#justAbove}).
         *
         * <p>Here because a reader that draws lines has to tell the two apart. A rule leaving a
         * position between two places bounds it and is owed its edge; one leaving it a single
         * string names a value, which is a distinction of the position and not a boundary on it.
         * Both are runs, and only the first is a bound.
         */
        public boolean holdsOneValue() {
            return after != null && after.equals(first.justAbove());
        }
    }

    /**
     * The language is not one run of the order with a string at either end.
     *
     * <p>What was established and not what was noticed. Reached only by having the language, having
     * asked, and having been answered — either there is no least string among the ones it admits,
     * or what it leaves above that least is not everything from some string upwards. Both are facts
     * about the strings, and neither is convexity: {@code startsWith("JP") || startsWith("US")} is
     * two runs and this says so, while a language that is one run whose ends no string names says
     * the same thing for another reason. What follows from either is that no edge is owed here, and
     * a reading that answered "not convex" would be answering a question nobody asked.
     *
     * <p>Never a fallback. A reader arriving here without having run the reading would be calling a
     * language something it had not looked at.
     */
    record NoNamedRun() implements TextExtent {}

    /**
     * The machines this needed were more than the allowance let it make.
     *
     * <p>A fact about this compiler. Which limit refused it is kept, since a language larger than
     * any one machine may be is one somebody wrote and can write differently, and an answer that
     * had already spent what it was allowed is not.
     */
    record NotBuilt(Meter.Stopped stopped) implements TextExtent {

        public NotBuilt {
            if (stopped == null) {
                throw new IllegalArgumentException("a construction that stopped was stopped by a limit");
            }
        }
    }
}
