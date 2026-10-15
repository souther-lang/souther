package souther.compiler.meaning;

import souther.compiler.check.ComparisonClaim;
import souther.compiler.numeric.Towards;

import java.util.Objects;

/**
 * How a relation a comparison states stands to the line of its author's it is a place of: which
 * line that is, what the line claims, and whether the relation is shown to be that line put on the
 * input, shown not to be, or neither.
 *
 * <p>Asked because a relation the statement turns on need not be where the author's line is. A
 * helper's {@code x <= 10} handed {@code if a > 0 then 10 else 11} turns at {@code a = 0}, and
 * {@code x} is eleven there: the statement changes across that place, and no value of {@code x}
 * stands at ten. A row at {@code a = 0} is no row at the line the author wrote.
 *
 * <p>A relation the comparison's own reading made is that line, put where the call put it. One made
 * by something a caller handed in — the condition of an {@code if} in an argument, a guard an
 * earlier call made — is where that turns, and this reading cannot say it is anywhere the author's
 * line is. Which of the three it is says what a reading is evidence of, and never which line or
 * which point is owed: those are the author's ({@link WrittenLine}), and so is what the line claims,
 * which is carried here so that a reading tied to nothing still says what it is a reading of.
 */
public sealed interface AuthoredPointMapping {

    /** Which of the author's lines the relation is a place of. */
    WrittenLine line();

    /**
     * What the author's line claims, as the comparison holds or fails across it: what the
     * comparison wrote, faced the way it wrote its two sides, for a line the comparison's own
     * relation draws; and for a line something else written in its definition draws — how an arm
     * is selected, a comparison written inside it, what an operation's law says — what the
     * comparison comes to across it, faced the one way ({@link #facedTheOneWay}), since the two
     * sides it wrote are not that line's. Which way a reading's quantity faces it is the
     * reading's.
     */
    ComparisonClaim claims();

    /**
     * The relation, put on the input: the author's line where the call put it.
     *
     * @param facing which way the relation faces the sides the comparison wrote, which is what
     *               says which side of the author's line each side of this one is where both sides
     *               of the line fail alike
     * @param itsOwn whether the comparison's own reading made the relation, so that it is the
     *               comparison's two sides held against each other: what the comparison wrote is
     *               then what the line claims, and its facing is what names the line's sides
     */
    record Proven(WrittenLine line, ComparisonClaim claims,
                  Derivation.AComparisonRead.Facing facing, boolean itsOwn)
            implements AuthoredPointMapping {

        public Proven {
            Objects.requireNonNull(line, "a relation is a place of some line");
            Objects.requireNonNull(claims, "a line claims something");
            Objects.requireNonNull(facing, "a relation faces its comparison some way, or none");
        }
    }

    /**
     * A place the statement turns that is no place of the author's line: everywhere the reading got
     * to on the way to the line, the comparison itself came out one way whatever the row.
     */
    record NotAnAuthoredBoundary(WrittenLine line, ComparisonClaim claims)
            implements AuthoredPointMapping {

        public NotAnAuthoredBoundary {
            Objects.requireNonNull(line, "a relation is a place of some line");
            Objects.requireNonNull(claims, "a line claims something");
        }
    }

    /** A place the statement turns that this reading cannot tie to the author's line either way. */
    record Undetermined(WrittenLine line, ComparisonClaim claims) implements AuthoredPointMapping {

        public Undetermined {
            Objects.requireNonNull(line, "a relation is a place of some line");
            Objects.requireNonNull(claims, "a line claims something");
        }
    }

    /**
     * {@code claim}, faced the one way: what holds of the line's own value, and for an order, that
     * it is satisfied below. For a claim no two written sides face, which is the only way two
     * readings facing it differently say one thing of it.
     */
    static ComparisonClaim facedTheOneWay(ComparisonClaim claim) {
        return switch (Objects.requireNonNull(claim, "a line claims something")) {
            case ComparisonClaim.Cut cut -> ComparisonClaim.Cut.satisfiedOn(Towards.BELOW,
                    cut.holdsAtTheValue());
            case ComparisonClaim.Singled singled -> singled;
        };
    }
}
