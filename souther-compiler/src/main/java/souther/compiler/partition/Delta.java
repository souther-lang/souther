package souther.compiler.partition;

import java.util.ArrayList;
import java.util.List;

/**
 * Where a row does not stand where its origin does.
 *
 * <p>One difference and two readers. How far a row is from what a reader recognises is the size
 * of this, and which fields a spread writes over is this projected onto the parameters — so the
 * order the search walks in and the row it writes come off one value. Counted two ways they
 * were free to disagree, and two positions under one parameter are two differences and one
 * field either way.
 *
 * <p>Read off the assignment and never off what the search reached for. A supporting position
 * the row stands at no class of is one no assignment moves, and counted as moved it put a row
 * one difference from its origin behind rows two away.
 *
 * @param at the positions, in the axes' own order
 */
public record Delta(List<Integer> at) {

public Delta {
        at = List.copyOf(at);
    }

    /**
     * Where {@code where} does not stand where {@code stands} does.
     *
     * <p>Both say where every position of one row is, so both are as long as there are positions.
     * Asked of one and read off the other, a pair that disagreed about how many positions there are
     * would come back as a distance rather than as the fault it is.
     */
public static Delta between(int[] stands, int[] where) {
        List<Integer> out = new ArrayList<>();
        for (int i = 0; i < where.length; i++) {
            if (where[i] != stands[i]) {
                out.add(i);
            }
        }
        return new Delta(out);
    }

    /** How far the row is from its origin. */
public int size() {
        return at.size();
    }

    /** Which of these positions are under {@code parameter}, which is what a spread over that
     *  parameter writes over. */
public List<Integer> under(List<Axis> axes, String parameter) {
        return at.stream().filter(i -> axes.get(i).path().head().equals(parameter)).toList();
    }
}
