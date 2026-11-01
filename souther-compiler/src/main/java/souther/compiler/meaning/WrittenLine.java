package souther.compiler.meaning;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Objects;

/**
 * One of the lines the author of a comparison drew: the arms taken, at the choices the comparison's
 * own definition writes, on the way to the relation that is the line.
 *
 * <p>{@code Int.max(x, y) <= g} draws two, one under each arm of the operation's cases; a
 * comparison whose definition chooses nothing on the way draws one, whatever a call hands it. Read
 * in each copy of the definition and the same in all of them, because the choices are the
 * definition's and so is the order they are met in. Where a caller put the line is the reading's
 * and not here.
 *
 * @param arms the arms, outermost first; empty for the comparison itself
 */
public record WrittenLine(List<Arm> arms) {

    /** The comparison itself, which is its one line where its definition chooses nothing. */
    public static final WrittenLine THE_COMPARISON = new WrittenLine(List.of());

    public WrittenLine {
        arms = List.copyOf(arms);
    }

    /**
     * The lines of one comparison in the order a reader that has nothing else to go on puts them
     * in: the arms taken, outermost first, each by its choice, then which arm, then whether it
     * selects; a line that is a prefix of another comes before it.
     *
     * <p>Total over the lines of one comparison: two lines it puts together are the same line.
     */
    public static Comparator<WrittenLine> inASteadyOrder() {
        Comparator<Arm> arm = Comparator.comparing(Arm::at, WrittenChoice.inASteadyOrder())
                .thenComparingInt(Arm::arm)
                .thenComparing(Arm::selects);
        return (one, other) -> {
            for (int at = 0; at < Math.min(one.arms().size(), other.arms().size()); at++) {
                int order = arm.compare(one.arms().get(at), other.arms().get(at));
                if (order != 0) {
                    return order;
                }
            }
            return Integer.compare(one.arms().size(), other.arms().size());
        };
    }

    /**
     * One arm taken at one choice.
     *
     * @param at      the choice
     * @param arm     which of its arms, counted from nought in the order the construct writes them;
     *                an {@code if}'s branch on its condition is nought and its other is one
     * @param selects whether the line is how the arm is selected rather than what it answers: the
     *                condition of an {@code if}, the standing of the arguments an operation's case
     *                is reached under
     */
    public record Arm(WrittenChoice at, int arm, boolean selects) {

        public Arm {
            Objects.requireNonNull(at, "an arm is of some choice");
            if (arm < 0) {
                throw new IllegalArgumentException("the arms of a choice are counted from nought: "
                        + arm);
            }
        }
    }

    /**
     * The choice this line is what one arm of answers — or null where it is the comparison
     * itself, a line under arms of more than one choice, or how an arm is selected.
     */
    public WrittenChoice choiceAnArmOfWhichItAnswers() {
        return arms.size() != 1 || arms.getFirst().selects() ? null : arms.getFirst().at();
    }

    /** This line, one arm further in. */
    WrittenLine then(Arm next) {
        List<Arm> more = new ArrayList<>(arms);
        more.add(next);
        return new WrittenLine(more);
    }
}
