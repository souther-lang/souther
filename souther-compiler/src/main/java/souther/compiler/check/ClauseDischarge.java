package souther.compiler.check;

import java.util.Optional;

/**
 * What one clause of the model owes a construction, and what this compiler could make of it: a
 * data's {@code invariant} (spec §invariant-discharge-capability) or a behavior's {@code ensures}
 * (spec §ensures-discharge-capability).
 *
 * <p>Once some clauses are statically dischargeable and others are not, the same {@code invariant}
 * keyword means two things to a reader: one shape reports an unguarded construction and the other
 * stays silent. Left implicit, an author believes a static guarantee exists where it does not.
 *
 * <p>Two values and not one word. The obligation is what the model says and does not move when this
 * compiler does; the capability is what this compiler managed and moves with every reading it gains
 * or loses. Answered as one, the classification was read off what the check happened to manage while
 * saying it was a property of the language, and the two sentences an author was shown — that a guard
 * would discharge this, that nothing would — were both about the checker.
 *
 * <p>One clause is one obligation and one answer, so there is one of these per clause and no way to
 * hold a clause with none. The answer is where the several live: it may hold several
 * {@link RequiredPart}s, every one of which has to be established, and a part may admit several
 * {@link StaticRoute}s, any one of which establishes it. That is the other half of the same point —
 * what is written as one thing need not be read as one thing — said with the two multiplicities kept
 * apart, since they are not the same one.
 *
 * <p>One record for both kinds of clause because it is one question — what a construction owes, and
 * what a guard could discharge. What follows from the answer is the reader's: for an invariant it
 * says what discharges a construction, for a rule how much of the relation there is to read.
 * Answering it twice would be two classifications to keep agreeing.
 *
 * <p>It is the clause's own capability, read with what it names assumed to stand for itself. A
 * construction that names nothing the check can name discharges nothing whatever its clauses say —
 * that is a fact about the construction, and belongs where the construction is.
 */
public record ClauseDischarge(DischargeObligation owed, CapabilityResult capability) {

    public ClauseDischarge {
        if (owed == null || capability == null) {
            throw new IllegalArgumentException(
                    "a clause owes establishment, and something came of trying to read it");
        }
    }

    /** The same classification under the name the clause was declared with, which is what an
     *  attempt's departure arm and a boundary issue call it. */
    public ClauseDischarge named(Optional<String> declared) {
        return new ClauseDischarge(owed.named(declared), capability);
    }
}
