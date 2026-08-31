package souther.compiler.check;

import java.util.ArrayList;
import java.util.List;

/**
 * What the rules of one value call a place in it.
 *
 * <p>A name and not a place. The rules of a {@code Holder} say {@code q.limit} and a row writes a
 * value under whichever case {@code q} turned out to be, so one of these stands at as many positions
 * as the cases a name crosses into. Resolving one is somebody else's answer, and the two directions
 * are not inverses: a name goes to a set of positions, and a position has one of these or none.
 *
 * <p>The second half of a {@link souther.compiler.inputs.RuleAddress} with the value left out —
 * which is what a reading of one declaration has to hand, since every name it writes is of the value
 * it is reading. An address is that value and this together, and two of these spelled alike under
 * different values are different addresses.
 *
 * <p><b>Fields, and nothing else.</b> A step into a sequence and a narrowing to a case are places a
 * value can be and are not names any rule of this value writes: what a record says relates the
 * fields it holds, and what a case says is written in the case. So there is no way to put one of
 * them in one of these, and a position reached through one has no name here rather than a name
 * nothing is written at.
 *
 * <p>Not {@link ClauseName}, which is what an author called a clause. That names the rule; this is
 * what the rule calls a place in the value it is written about.
 *
 * <p>The steps are the meaning and the spelling is not. {@link #toString()} is for a report and for
 * a reader of this compiler; a table is keyed by the steps, so a name is never taken apart again by
 * looking for the dots in it.
 *
 * @param steps the fields read from the value, in the order they are read. Empty is the value
 *              itself, which is what a rule writing {@code value >= 0} of a newtype names
 */
public record RuleKey(List<String> steps) {

    /** The value whose rules these are. A newtype's own {@code value} is this and not a step:
     *  wearing a name is not being somewhere else. */
    public static final RuleKey THE_VALUE = new RuleKey(List.of());

    public RuleKey {
        for (String step : steps) {
            if (step == null || step.isEmpty()) {
                throw new IllegalArgumentException("a field a rule names is called something");
            }
            if (step.indexOf('.') >= 0) {
                throw new IllegalArgumentException(
                        "`" + step + "` is two names run together, and a step is one field: " + steps);
            }
        }
        steps = List.copyOf(steps);
    }

    /** The name of one field of the value. */
    public static RuleKey of(String field) {
        return new RuleKey(List.of(field));
    }

    /** This name with {@code field} read from what it reaches. */
    public RuleKey then(String field) {
        List<String> longer = new ArrayList<>(steps);
        longer.add(field);
        return new RuleKey(longer);
    }

    /**
     * This name, read from {@code field} of the value one out.
     *
     * <p>What a rule of the outer value calls what a rule of the inner one called this. The rules
     * of a {@code Holder} name {@code q.limit} where the rules of {@code q}'s type name
     * {@code limit}, and rebasing is prepending the field the inner value was reached by.
     */
    public RuleKey readFrom(String field) {
        List<String> longer = new ArrayList<>();
        longer.add(field);
        longer.addAll(steps);
        return new RuleKey(longer);
    }

    /** Whether this is the value the rules are of, rather than anything in it. */
    public boolean isTheValueItself() {
        return steps.isEmpty();
    }

    /**
     * Whether this is {@code other} or a name under it.
     *
     * <p>Of the steps and never of the spelling. A name is a list of fields, so {@code ab} is not
     * under {@code a} — which a reader comparing the text has to remember to say, and says by
     * naming the separator.
     */
    public boolean isAtOrUnder(RuleKey other) {
        return steps.size() >= other.steps.size()
                && steps.subList(0, other.steps.size()).equals(other.steps);
    }

    /** For a report and for a reader of this compiler. Never how a name is compared or looked up. */
    @Override
    public String toString() {
        return String.join(".", steps);
    }
}
