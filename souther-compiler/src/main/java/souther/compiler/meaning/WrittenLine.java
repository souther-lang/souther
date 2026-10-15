package souther.compiler.meaning;

import java.util.ArrayList;
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

    /** This line, one arm further in. */
    WrittenLine then(Arm next) {
        List<Arm> more = new ArrayList<>(arms);
        more.add(next);
        return new WrittenLine(more);
    }
}
