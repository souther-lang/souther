package souther.compiler.query;

import souther.compiler.publish.CanonicalSelection;

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
 * <p>What is outside the count keeps every reason it is out. Nothing was read against it and nothing
 * has shown a row can be written there are independent, and a fold that split them into a list
 * apiece would be choosing which reason a reader is told — and would go quiet about a reason nobody
 * had added a list for. The reasons are read where they are worded, and there they are read
 * exhaustively.
 *
 * @param <T> what carries an obligation here — a point of a behavior's account, or one of a
 *            declaration's debts with the declarations that owe it
 */
public record ObligationSummary<T>(List<T> met, List<T> unmet, List<T> undecided,
                                   List<Excluded<T>> excluded) {

    /** One obligation outside the count, with every reason it is out. */
    public record Excluded<T>(T item, CanonicalSelection<ObligationDisposition.Reason> because) {

        public Excluded {
            if (because == null || because.isEmpty()) {
                throw new IllegalArgumentException(
                        "an obligation left out of the count says why it is out");
            }
        }

        /** Whether {@code reason} is one of them, for a reader wording that reason. */
        public boolean was(ObligationDisposition.Reason reason) {
            return because.written().contains(reason);
        }
    }

    public ObligationSummary {
        met = List.copyOf(met);
        unmet = List.copyOf(unmet);
        undecided = List.copyOf(undecided);
        excluded = List.copyOf(excluded);
    }

    /** How many obligations the count holds, which is the denominator a block prints. */
    public int counted() {
        return met.size() + unmet.size() + undecided.size();
    }

    /** The ones left out for {@code reason}, in the order they were given. */
    public List<T> excludedBy(ObligationDisposition.Reason reason) {
        return excluded.stream().filter(each -> each.was(reason)).map(Excluded::item).toList();
    }

    /** Where each of {@code items} stands, in the order they were given. */
    public static <T> ObligationSummary<T> of(List<T> items, Function<T, ObligationAssessment> owed) {
        List<T> met = new ArrayList<>();
        List<T> unmet = new ArrayList<>();
        List<T> undecided = new ArrayList<>();
        List<Excluded<T>> excluded = new ArrayList<>();
        for (T each : items) {
            switch (owed.apply(each).disposition()) {
                case ObligationDisposition.Met _ -> met.add(each);
                case ObligationDisposition.Unmet _ -> unmet.add(each);
                case ObligationDisposition.Undecided _ -> undecided.add(each);
                case ObligationDisposition.NotCounted it ->
                        excluded.add(new Excluded<>(each, it.because()));
            }
        }
        return new ObligationSummary<>(met, unmet, undecided, excluded);
    }
}
