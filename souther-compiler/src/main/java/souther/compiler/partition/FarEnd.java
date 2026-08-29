package souther.compiler.partition;

import souther.compiler.numeric.Towards;

/**
 * What settled where a run of a quantity's values stops, away from the line a border drew.
 *
 * <p>A border's point away from its line asks for a row somewhere inside the run beside it, and
 * where that run stops on the far side is what tells one such point from another. So this is what a
 * row there is owed to, beside the line itself.
 *
 * <p><b>Three answers, and they are answers to three different questions.</b> A rule can have put a
 * line there, and then the run is that rule's as much as the border's own — an author can move it
 * without touching anything else, and each rule that drew a line at the place is enough on its own,
 * so each is one of these. The rules can leave the quantity nothing past a place, and that is not
 * one rule's doing: it is what every rule about the position leaves together, with the order's own
 * extent among them, so what settles the run is the place and there is no line to name. Or nothing
 * stops it, and the run goes as far as the order does.
 *
 * <p><b>The line and where it falls, and not the line alone.</b> A rule is read on whatever the
 * quantity is at the position it was met at, and one rule can be read against two quantities — the
 * same comparison over a form and over a multiple of that form parts values that are not the same
 * values. Told apart by the rule alone, two runs that stop in two places would be one.
 */
public sealed interface FarEnd {

    /**
     * A rule put a line there.
     *
     * @param line  which line of the model, which is what an author can move
     * @param where the place it parts the values, written the one way so that two spellings of one
     *              division are one end
     */
    record AtALine(AuthoredLine line, Seam where) implements FarEnd {

        public AtALine {
            if (line == null || where == null) {
                throw new IllegalArgumentException(
                        "a line is some rule's, somewhere: " + line + " " + where);
            }
            where = where.canonical();
        }
    }

    /**
     * The rules leave the quantity nothing past there.
     *
     * <p>The place and no line, because no one rule put it there. Which declarations could have
     * moved it is a question about the reading that produced the end, and a row inside the run is
     * owed to the end rather than to any one of them.
     */
    record AtTheDomain(Bound reaches) implements FarEnd {

        public AtTheDomain {
            if (reaches == null) {
                throw new IllegalArgumentException("an end the rules leave is somewhere");
            }
            reaches = reaches.canonical();
        }
    }

    /** Nothing stops the run that way: it goes as far as the order does. */
    record AtTheOrderEnd(Towards towards) implements FarEnd {

        public AtTheOrderEnd {
            if (towards == null) {
                throw new IllegalArgumentException("an end of the order is one of its two");
            }
        }
    }
}
