package souther.compiler.check;

/**
 * What a rule filed at one place is about.
 *
 * <p>Asked only where a reading stopped. A comparison the arithmetic read to the end has a subject
 * already — the quantity it cuts — and nothing here would add to it; where it stopped there is no
 * subject, and this is what stands in its place.
 *
 * <p>Made by {@link UnreadComparison#subjectAt}, so the law is one. Which side of a comparison a
 * position stands as is the same question for a clause of a declaration and for a body's
 * comparison, and each reader answering it in its own names is how the two came to disagree about
 * one shape of rule in the first place. What a reader is asked for is the part only it knows: what
 * the place it chose is called, and whether that place is the position's own value or a number
 * taken of it.
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

    /**
     * The rule constrains the values that stand at the position.
     *
     * <p>So what the position carries is the rule's own subject, and whether a line can be drawn on
     * it is a question about this rule. The position is here because that question is asked of it.
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
     *
     * <p>Carrying nothing, because there is nothing to ask of the position here. Held with the
     * place it was filed at, this would be a position beside an answer that is not about it, which
     * is the reading the whole type exists to stop.
     */
    record NotAboutOwnValues<K>() implements RuleAt<K> {}
}
