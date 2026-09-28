package souther.compiler.partition;

import java.util.Objects;

/**
 * One thing a plan asks a generation to look for, of whichever kind it is.
 *
 * <p>Closed, so that a reader answering for every kind a plan can hold writes a case for each of
 * them rather than falling through to one that happens to compile. {@link GenerationPlan} hands a
 * search four lists because each kind is searched its own way; a reader standing on the far side of
 * a search — asking what a run was for and what came of it — has no such reason to keep them apart,
 * and a reader that rebuilt its own universe one list at a time was the reader a class of obligation
 * went missing from without anything failing to compile.
 *
 * <p>A class and a combination of two classes are named by the {@link ObligationIdentity} a row is
 * weighed against — {@link ObligationIdentity.OfAClass} and {@link ObligationIdentity.OfAFallbackPairCell}
 * are already that identity, and a combination of a body's decisions is the same again
 * ({@link ObligationIdentity.OfACombinationOfDecisions}). An arm is not: what steers a candidate is
 * {@link Generator.ArmOwed}, an occurrence a search is put to, and the identity a row is offered
 * under is the arm the author wrote — a different reading, taken by whoever already holds a map from
 * one to the other, which is not this.
 */
public sealed interface GenerationObligation
        permits GenerationObligation.Class, GenerationObligation.Arm, GenerationObligation.Pair,
                GenerationObligation.Meeting {

    /** A class of a position no row sits in, in the search's own words. */
    record Class(ClassOfAPosition target) implements GenerationObligation {

        public Class {
            Objects.requireNonNull(target, "a class a plan asks for is some class");
        }
    }

    /** An arm of the body no row goes through, named by the occurrences a search is put to. */
    record Arm(Generator.ArmOwed target) implements GenerationObligation {

        public Arm {
            Objects.requireNonNull(target, "an arm a plan asks for is some arm");
        }
    }

    /** A combination of two classes no row is in, where the pair space is the criterion. */
    record Pair(ObligationIdentity.OfAFallbackPairCell target) implements GenerationObligation {

        public Pair {
            Objects.requireNonNull(target, "a combination a plan asks for is some combination");
        }
    }

    /** A combination of the body's decisions no row makes, where those are the criterion. */
    record Meeting(ObligationIdentity.OfACombinationOfDecisions target)
            implements GenerationObligation {

        public Meeting {
            Objects.requireNonNull(target, "a meeting a plan asks for is some meeting");
        }
    }
}
