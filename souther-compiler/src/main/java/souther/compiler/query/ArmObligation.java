package souther.compiler.query;

import souther.compiler.coverage.CoverageSites;

import java.util.List;
import java.util.Set;

/**
 * One arm an author wrote, and what this compilation found out about it.
 *
 * <p>The normal form of the arm account. Everything a surface says about arms — the two numbers, the
 * arms named as gaps, the arms marked as open, the arms left out and why — is a projection of a list
 * of these, so no two surfaces can disagree about one arm.
 *
 * <p>Per arm and not per occurrence. A non-recursive helper is spliced into every body that calls
 * it, so one arm the author wrote is several arms in the tree that runs; covering the same arm
 * through a second call site establishes nothing the first did not. The occurrences are carried
 * because they are what was read — each is emitted, probed and reasoned about on its own — and what
 * the arm came to is one answer over all of them.
 */
public sealed interface ArmObligation {

    /** Every copy of this arm, in the order the body holds them. Never empty. */
    List<CoverageSites.Site> occurrences();

    /** Where this stands in the account, which is the one question asked of it. */
    ArmDisposition disposition();

    /** What tells this arm from every other, which its occurrences share. */
    default CoverageSites.Obligation id() {
        return occurrences().getFirst().obligation();
    }

    /**
     * The occurrence a reader is shown, which is where to look and not where the arm is.
     *
     * <p>Where the copies keep the positions they were written at they all say the same thing; where
     * a copy could not — the body came from a module this compile has no source for, so each copy
     * was given the call site that spliced it — the occurrences are at different places and one of
     * them has to be the one shown, since the arm is one arm and a report says it once. What each
     * occurrence carries says the arm is written out of sight and names the declaration, so a report
     * says that however this chooses; the choice only decides which call the reader is shown.
     */
    default CoverageSites.Site display() {
        return occurrences().getFirst();
    }

    /**
     * An arm the count holds, with what the rows came to about it.
     *
     * <p>Three states and no fourth. A row through the arm is a positive fact that nothing else
     * takes back, so {@code Partial(Hit)} says something that cannot happen: a reading that stopped
     * short leaves the arms it did not light open and the arms it lit alight. The two states with no
     * value are not here either — where nothing read the rows there is no arm account at all, and a
     * counted arm carrying one of them would be an account holding an arm it cannot answer for.
     */
    record Counted(List<CoverageSites.Site> occurrences, Measurement<ArmCoverage> coverage)
            implements ArmObligation {

        public Counted {
            occurrences = oneArm(occurrences);
            switch (coverage) {
                case Measurement.Complete<ArmCoverage> _ -> { }
                case Measurement.Partial<ArmCoverage> it -> {
                    if (ArmCoverage.hit(it.value())) {
                        throw new IllegalArgumentException(
                                "a row through an arm went through it whatever else stopped: "
                                        + occurrences.getFirst().obligation());
                    }
                }
                case Measurement.FailedToMeasure<ArmCoverage> _,
                     Measurement.NotMeasured<ArmCoverage> _ -> throw new IllegalArgumentException(
                        "an arm the count holds is one the rows were read against: "
                                + occurrences.getFirst().obligation());
            }
        }

        @Override
        public ArmDisposition disposition() {
            if (coverage.made().map(ArmCoverage::hit).orElse(false)) {
                return ArmDisposition.MET;
            }
            return coverage.weakening().isEmpty()
                    ? ArmDisposition.UNMET : ArmDisposition.UNDECIDED;
        }
    }

    /** An arm outside the count, with why it is out. */
    record NotCounted(List<CoverageSites.Site> occurrences, ArmExclusion because)
            implements ArmObligation {

        public NotCounted {
            occurrences = oneArm(occurrences);
            java.util.Objects.requireNonNull(because, "an arm left out of the count says why");
        }

        @Override
        public ArmDisposition disposition() {
            return ArmDisposition.NOT_COUNTED;
        }
    }

    /**
     * What became of one arm, over every occurrence of it and everything that was read.
     *
     * <p>The one place an arm's state is decided. Going through an arm is going through it whichever
     * call site the row arrived by, so one occurrence lit is the arm lit; and an arm nothing lit is
     * a gap where the rows ran out and a question where they did not. Both halves are settled here,
     * from what was observed, and nothing downstream works either of them out again.
     *
     * @param occurrences every copy of the arm, in the order the body holds them
     * @param covered     the probes some row went through
     * @param rowsUnread  what the reading of this behavior's rows went without, which is empty
     *                    where it read them all
     */
    static ArmObligation of(List<CoverageSites.Site> occurrences, Set<Integer> covered,
                            WeakeningSet rowsUnread) {
        // An obligation whose occurrences were put together without anything establishing that they
        // are one is not one the rows can answer: a row through either of them may or may not be a
        // row through this one, and a hit or a miss over them is a number about however many rules
        // that is.
        if (!occurrences.getFirst().obligation().decided().isSettled()) {
            return new NotCounted(occurrences, new ArmExclusion.OccurrencesNotToldApart(
                    occurrences.getFirst().obligation().origin()));
        }
        if (occurrences.stream().anyMatch(site -> covered.contains(site.index()))) {
            return new Counted(occurrences, new Measurement.Complete<>(new ArmCoverage.Hit()));
        }
        return new Counted(occurrences, rowsUnread.isEmpty()
                ? new Measurement.Complete<>(new ArmCoverage.NoHit())
                : new Measurement.Partial<>(new ArmCoverage.NoHit(), rowsUnread));
    }

    /** The occurrences of one arm, which is what an entry of this account is over. */
    private static List<CoverageSites.Site> oneArm(List<CoverageSites.Site> occurrences) {
        if (occurrences == null || occurrences.isEmpty()) {
            throw new IllegalArgumentException("an arm is somewhere the body holds it");
        }
        CoverageSites.Obligation id = occurrences.getFirst().obligation();
        for (CoverageSites.Site each : occurrences) {
            if (!id.equals(each.obligation())) {
                throw new IllegalArgumentException(
                        "the occurrences of one arm are of one arm: " + id + " with "
                                + each.obligation());
            }
        }
        return List.copyOf(occurrences);
    }
}
