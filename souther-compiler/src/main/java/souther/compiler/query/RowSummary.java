package souther.compiler.query;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * What a behavior's rows owe by way of answers, in the groups a surface counts and names them in.
 *
 * <p>The one thing a consumer of the row account reads. The document's entries and the findings a
 * build refuses over are projections of this, and a surface that decided for itself which rows are
 * waiting would be a second answer to a question the source has already settled — which is the
 * arrangement this exists to have none of.
 *
 * <p><b>Everything the numbers hold is in {@link #all}, once.</b> The denominator is
 * {@link #counted()} and every row in it is in exactly one of {@link #met()} and {@link #unmet()},
 * so a surface that prints the two numbers and then walks the second has said what the difference
 * between them is.
 *
 * <p><b>And the denominator needs no qualification.</b> Where the arm account carries a census
 * because the set of arms it counted may be short of the set a behavior owes, the rows are read off
 * the text: a row whose answer no parse could read is malformed, is reported as that, and is not a
 * row this is short of.
 */
public record RowSummary(List<RowObligation> all) {

    public RowSummary {
        all = List.copyOf(Objects.requireNonNull(all, "an account is a list of what it holds"));
    }

    /** The rows that state what they expect. */
    public List<RowObligation> met() {
        return in(RowDisposition.MET);
    }

    /** The rows written {@code <?>}. One finding each. */
    public List<RowObligation> unmet() {
        return in(RowDisposition.UNMET);
    }

    /** How many rows the answers are counted over. */
    public int counted() {
        return all.size();
    }

    private List<RowObligation> in(RowDisposition where) {
        List<RowObligation> out = new ArrayList<>();
        for (RowObligation each : all) {
            if (each.disposition() == where) {
                out.add(each);
            }
        }
        return List.copyOf(out);
    }
}
