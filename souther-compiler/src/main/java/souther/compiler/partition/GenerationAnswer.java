package souther.compiler.partition;

import java.util.Objects;

/**
 * What became of one thing a plan asked a generation for, the obligation and the answer held as
 * one value.
 *
 * <p>Closed over the same four kinds {@link GenerationObligation} is, and each variant pairs one
 * obligation of a kind with the disposition that kind is answered in: an arm's is an
 * {@link ArmDisposition} and carries the place a row went through; the other three are answered
 * in a {@link ClassDisposition}. A variant naming an obligation of one kind beside a disposition
 * of the wrong shape is not a value this can hold, which is what stops a class's row from being
 * filed under an arm's answer or the reverse.
 *
 * <p><b>Not one disposition type made to fit every kind.</b> An arm's answer and a class's answer
 * are not the same news read two ways: an arm may have nowhere to look at all
 * ({@link ArmDisposition.NoWayIn}), which nothing asks a class, and where a row was composed an
 * arm's says which splice it went through ({@link ArmDisposition.Built#at}) and a class's says
 * nothing of the kind. Folding the two into one shared disposition to make this a uniform map
 * would either invent a place for {@code at} on every kind or lose it from the one kind that has
 * it — which is the flattening the sealed pairing here exists to refuse. What is uniform is the
 * obligation → answer filing, not the answer's shape.
 *
 * <p>The obligation and not only the target it is asked at. {@link Discharge} files these by the
 * obligation the plan named, and a value that knew its disposition alone would leave that filing
 * to be redone from whichever key a map happened to hold it under.
 */
public sealed interface GenerationAnswer
        permits GenerationAnswer.Class, GenerationAnswer.Arm, GenerationAnswer.Pair,
                GenerationAnswer.Meeting {

    /** The obligation this is an answer to. */
    GenerationObligation obligation();

    /** What became of one class the plan asked for. */
    record Class(GenerationObligation.Class obligation, ClassDisposition disposition)
            implements GenerationAnswer {

        public Class {
            Objects.requireNonNull(obligation, "an answer is to some obligation");
            Objects.requireNonNull(disposition, "an answer says what became of the obligation");
        }
    }

    /** What became of one arm the plan asked for. */
    record Arm(GenerationObligation.Arm obligation, ArmDisposition disposition)
            implements GenerationAnswer {

        public Arm {
            Objects.requireNonNull(obligation, "an answer is to some obligation");
            Objects.requireNonNull(disposition, "an answer says what became of the obligation");
        }
    }

    /** What became of one combination of two classes the plan asked for. */
    record Pair(GenerationObligation.Pair obligation, ClassDisposition disposition)
            implements GenerationAnswer {

        public Pair {
            Objects.requireNonNull(obligation, "an answer is to some obligation");
            Objects.requireNonNull(disposition, "an answer says what became of the obligation");
        }
    }

    /** What became of one meeting of the body's decisions the plan asked for. */
    record Meeting(GenerationObligation.Meeting obligation, ClassDisposition disposition)
            implements GenerationAnswer {

        public Meeting {
            Objects.requireNonNull(obligation, "an answer is to some obligation");
            Objects.requireNonNull(disposition, "an answer says what became of the obligation");
        }
    }
}
