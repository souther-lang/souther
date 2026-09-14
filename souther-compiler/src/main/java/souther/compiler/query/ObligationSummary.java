package souther.compiler.query;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

/**
 * What a set of obligations came to, in the groups a report counts and names them in.
 *
 * <p>One fold for every place that reports obligations. A behavior's own and its module's
 * declarations' are two projections of one relation and are printed in two blocks, and a block that
 * worked its own groups out could count what the other names and name what the other counts. The
 * denominator here is {@link #counted()} and every obligation is in exactly one of {@link #met()},
 * {@link #unmet()} and {@link #undecided()}, so a block that prints the number and then walks the
 * last two has said which obligations the difference is.
 *
 * <p><b>Nothing is left out.</b> Every obligation handed to this is one the model owes a row at, and
 * what this compiler could not read, compose or represent is news about the point rather than about
 * whether it is owed. There was a fourth group for obligations the account dropped, and what it
 * dropped them for was the absence of a showing that a row could be written — so a field nobody
 * could compose a value for shrank the denominator its siblings were counted in (issue #1249). What
 * is not known about a point is now said of a point that is counted, which is
 * {@link ObligationDisposition.Undecided}.
 *
 * @param <T> what carries an obligation here — a point of a behavior's account, or one of a
 *            declaration's debts with the declarations that owe it
 */
public record ObligationSummary<T>(List<T> met, List<T> unmet, List<T> undecided) {

    public ObligationSummary {
        met = List.copyOf(met);
        unmet = List.copyOf(unmet);
        undecided = List.copyOf(undecided);
    }

    /** How many obligations the count holds, which is the denominator a block prints. */
    public int counted() {
        return met.size() + unmet.size() + undecided.size();
    }

    /** The undecided ones this question is open about, in the order they were given. */
    public List<T> undecidedBy(ObligationDisposition.Uncertainty question,
                               Function<T, ObligationAssessment> owed) {
        return undecided.stream()
                .filter(each -> owed.apply(each).disposition()
                        instanceof ObligationDisposition.Undecided it
                        && it.because().written().contains(question))
                .toList();
    }

    /** Where each of {@code items} stands, in the order they were given. */
    public static <T> ObligationSummary<T> of(List<T> items, Function<T, ObligationAssessment> owed) {
        List<T> met = new ArrayList<>();
        List<T> unmet = new ArrayList<>();
        List<T> undecided = new ArrayList<>();
        for (T each : items) {
            switch (owed.apply(each).disposition()) {
                case ObligationDisposition.Met _ -> met.add(each);
                case ObligationDisposition.Unmet _ -> unmet.add(each);
                case ObligationDisposition.Undecided _ -> undecided.add(each);
            }
        }
        return new ObligationSummary<>(met, unmet, undecided);
    }
}
