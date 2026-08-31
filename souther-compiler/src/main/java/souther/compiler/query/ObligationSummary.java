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
 * denominator here is {@link #counted()} and every obligation in it is in exactly one of
 * {@link #met()}, {@link #unmet()} and {@link #undecided()}, so a block that prints the number and
 * then walks the last two has said which obligations the difference is.
 *
 * <p>The two groups outside the count are said and not counted, and an obligation may be in both:
 * nothing was read against it and nothing has shown a row can be written there are independent, and
 * a fold choosing one of them would be deciding which reason a reader is told.
 *
 * @param <T> what carries an obligation here — a point of a behavior's account, or one of a
 *            declaration's debts with the declarations that owe it
 */
public record ObligationSummary<T>(List<T> met, List<T> unmet, List<T> undecided,
                                   List<T> nothingWasRead, List<T> notKnownWritable) {

    public ObligationSummary {
        met = List.copyOf(met);
        unmet = List.copyOf(unmet);
        undecided = List.copyOf(undecided);
        nothingWasRead = List.copyOf(nothingWasRead);
        notKnownWritable = List.copyOf(notKnownWritable);
    }

    /** How many obligations the count holds, which is the denominator a block prints. */
    public int counted() {
        return met.size() + unmet.size() + undecided.size();
    }

    /** Where each of {@code items} stands, in the order they were given. */
    public static <T> ObligationSummary<T> of(List<T> items, Function<T, ObligationAssessment> owed) {
        List<T> met = new ArrayList<>();
        List<T> unmet = new ArrayList<>();
        List<T> undecided = new ArrayList<>();
        List<T> unread = new ArrayList<>();
        List<T> unwritable = new ArrayList<>();
        for (T each : items) {
            switch (owed.apply(each).disposition()) {
                case ObligationDisposition.Met _ -> met.add(each);
                case ObligationDisposition.Unmet _ -> unmet.add(each);
                case ObligationDisposition.Undecided _ -> undecided.add(each);
                case ObligationDisposition.NotCounted it -> {
                    if (it.because().contains(ObligationDisposition.Reason.NOTHING_WAS_READ)) {
                        unread.add(each);
                    }
                    if (it.because()
                            .contains(ObligationDisposition.Reason.NOT_KNOWN_TO_BE_WRITABLE)) {
                        unwritable.add(each);
                    }
                }
            }
        }
        return new ObligationSummary<>(met, unmet, undecided, unread, unwritable);
    }
}
