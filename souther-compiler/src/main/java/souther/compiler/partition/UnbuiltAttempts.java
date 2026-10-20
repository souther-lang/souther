package souther.compiler.partition;

import java.util.Objects;

/**
 * What several attempts to compose a container, none of which built one, came to together.
 *
 * <p>The attempts stop for different reasons, and a reader is owed all of them: a figure that cut
 * one short is somebody's to raise whatever another attempt came to, and a population one walked
 * in part is no less so for a later attempt having found nothing at all. Kept as the last attempt
 * alone, an attempt that met a figure is told as one that did not as soon as another follows it.
 *
 * <p>Joined as the other walks over alternatives join theirs ({@code ContainersAddingUp},
 * {@code TermRealizations#firstThatBuilds}): what each came to without is joined
 * ({@link CompositionShortfall#and}), so the figures, the numbers it could not hold and the
 * repertoire it did not write are each kept, and a walk that saw only part of what there is stays
 * one that did not see the whole.
 */
final class UnbuiltAttempts {

    private CompositionShortfall met = CompositionShortfall.NONE;
    private TermRealizations.Realization last;
    private String detail;

    /** Takes in one attempt that built nothing. */
    void add(TermRealizations.Realization one) {
        if (one instanceof TermRealizations.Realization.Built) {
            throw new IllegalArgumentException(
                    "an attempt that built something is not one that built nothing");
        }
        met = met.and(one.shortfall());
        last = one;
        if (detail == null && one instanceof TermRealizations.Realization.Unexhausted walked) {
            detail = walked.detail();
        }
    }

    /**
     * What a composing that built nothing comes to: a stop at a figure of any attempt's or of
     * {@code besides}, else a walk that saw part of what there is, else what the last attempt found
     * of the model, else {@code nothing}.
     *
     * @param besides what the composing met apart from the attempts
     * @param nothing what is said where no attempt was made
     */
    TermRealizations.Realization came(CompositionShortfall besides,
                                      TermRealizations.Realization nothing) {
        Objects.requireNonNull(nothing, "what is said of a composing no attempt spoke for");
        CompositionShortfall together = besides.and(met);
        if (!together.figures().isEmpty()) {
            return new TermRealizations.Realization.Stopped(together);
        }
        if (!together.nothing()) {
            return new TermRealizations.Realization.Unexhausted(together, detail);
        }
        return last != null ? last : nothing;
    }
}
