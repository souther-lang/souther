package souther.compiler.check;

import souther.compiler.diag.SourcePos;

import java.util.Optional;

/**
 * What a construction owes for one clause of the model: that the clause holds of the value being
 * built.
 *
 * <p>Raised by the clause being written, and by nothing else. Nothing about what this compiler made
 * of the clause reaches here — the obligation is the same on the day the check learns to read one
 * more shape and on the day it forgets one. Read off the reading instead, a clause nothing could be
 * made of would be a clause nothing was owed for, and a construction would come back accounted for
 * because the analysis was the weaker of the two.
 *
 * <p>Exactly one per clause, which is where this accounting differs from the coverage one. A rule of
 * the model raises as many questions as it states things about, and each of them has one answer
 * ({@link Required}, {@link RuleAccounting}); a clause of an invariant raises this one question
 * however many ways it turns out to be readable ({@link StaticReading}). The multiplicity is on
 * opposite sides, which is why the two are not one accounting and share no type.
 *
 * @param clause where the clause is written, which is the position an author acts at
 * @param name   what the clause was declared as, where it was declared with one — which is what an
 *               attempted construction's departure arm and a boundary issue call it
 */
public record DischargeObligation(SourcePos clause, Optional<String> name) {

    public DischargeObligation {
        if (clause == null || name == null) {
            throw new IllegalArgumentException("an obligation is about a clause that was written");
        }
    }

    /** An obligation not yet attributed to a declared clause: the capability is read off the
     *  expression, and the name is attached where the declaration is. */
    public DischargeObligation(SourcePos clause) {
        this(clause, Optional.empty());
    }

    /** The same obligation under the name the clause was declared with. */
    public DischargeObligation named(Optional<String> declared) {
        return new DischargeObligation(clause, declared);
    }
}
