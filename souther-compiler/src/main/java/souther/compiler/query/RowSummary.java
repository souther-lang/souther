package souther.compiler.query;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * What a behavior's rows owe by way of answers.
 *
 * <p>The one thing a consumer of the row account reads. The document's entries and the findings a
 * build refuses over are projections of this, and a surface that decided for itself which rows are
 * waiting would be a second answer to a question the source has already settled — which is the
 * arrangement this exists to have none of.
 *
 * <p><b>Everything is in {@link #all}, once.</b> The document publishes it whole, and the findings
 * are the part of it that is waiting, so what a build acts on and what a consumer looks the row up
 * in cannot come apart.
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

    /** The rows written {@code <?>}. One finding each. */
    public List<RowObligation> unmet() {
        List<RowObligation> out = new ArrayList<>();
        for (RowObligation each : all) {
            if (each.disposition() == RowDisposition.UNMET) {
                out.add(each);
            }
        }
        return List.copyOf(out);
    }
}
