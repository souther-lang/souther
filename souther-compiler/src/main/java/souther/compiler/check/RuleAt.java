package souther.compiler.check;

/**
 * What a rule filed at one place is about, said by the reader that filed it there.
 *
 * <p>Asked only where a reading stopped. A comparison the arithmetic read to the end has a subject
 * already — the quantity it cuts — and nothing here would add to it; where it stopped there is no
 * subject, and this is what stands in its place.
 *
 * <p>The one question a classifier of comparisons cannot answer for itself. Whether a rule
 * constrains the values at a position, or something taken from them, is not readable off the
 * expression: {@link ValueOrigin} reads a call through to its body, so {@code describe(a) > 0}
 * arrives as arithmetic holding the position and carries no operation to recognise. What settles it
 * is what the reader knew when it chose the place to file at.
 *
 * <p>Two cases, and the second is named for what it denies because there is nothing the members of
 * it hold in common besides that. A length taken of a string, a value a call answered of a field,
 * and a position met inside an expression the reader did not take apart are one case only in that
 * none of them says anything about the order the position's own values carry. Called a quantity of
 * the position, two of the three are not one; called something of it, the one thing this is for
 * disappears from the name.
 *
 * @param <K> what the reader calls a position
 */
public sealed interface RuleAt<K> {

    /** The position this stands for, in the reader's own names. */
    K position();

    /**
     * The rule constrains the values that stand at the position.
     *
     * <p>So what the position carries is the rule's own subject, and whether a line can be drawn on
     * it is a question about this rule.
     */
    record AboutOwnValues<K>(K position) implements RuleAt<K> {

        public AboutOwnValues {
            if (position == null) {
                throw new IllegalArgumentException("a rule about a position's values names it");
            }
        }
    }

    /**
     * The rule is filed here and states nothing about the values that stand here.
     *
     * <p>The carrier is not this rule's subject, so asking whether a line can be drawn on it
     * answers about something the author did not write. A rule about {@code String.length(s)} told
     * that no line is drawn on a string sends its author to the values of {@code s}, which the rule
     * never mentions.
     */
    record NotAboutOwnValues<K>(K position) implements RuleAt<K> {

        public NotAboutOwnValues {
            if (position == null) {
                throw new IllegalArgumentException("a rule filed at a position names it");
            }
        }
    }
}
