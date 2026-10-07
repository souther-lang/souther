package souther.compiler.partition;

import souther.compiler.carrier.Membership;
import souther.compiler.check.StatedComparison;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.types.ValueName;

import java.util.Set;

/**
 * Which of a body's conditions the decision table holds as distinctions over what a dependency
 * answered.
 *
 * <p>A row controls two things: what it writes at a position and what it stands a dependency in
 * with. The reading of the input is a reading of the first, and a condition about the second is not
 * its subject — so where it reads nothing of such a condition, that is a condition belonging to the
 * other reading and not one this compiler failed to read. Said as the second, a body every row of
 * which takes both ways through {@code known(name)} was held undetermined over a distinction the
 * decision table had already named and seen taken.
 *
 * <p><b>The decision table's own answer, asked rather than worked out again.</b> What a dependency's
 * answer is and when a comparison is a proposition over one are {@link DecisionSubjects} and
 * {@link DecisionComparison}; the decision reading is made from this value, so a condition the
 * reading of the input hands over is one that reading names. A reader that recognised calls to
 * dependencies for itself would hand over conditions the table holds no column for, and those
 * would leave the account as read by nobody.
 *
 * <p>Only conditions over an answer. A truth of a position is a subject a row controls as well, and
 * it is the reading of the input's: a part of it that reading left unread is still unread.
 */
record WhatAnAnswerTakesUp(DecisionSubjects subjects, DecisionComparison comparisons) {

    /**
     * What the decision table over {@code read} takes up, where the body depends on
     * {@code dependencies}.
     *
     * <p>Given none, nothing is taken up: a rule nothing stands a dependency in for has no answer in
     * it a row controls, which is what a declaration's clause is.
     */
    static WhatAnAnswerTakesUp of(InputReading read, Set<ValueName.Behavior> dependencies) {
        DecisionSubjects subjects =
                new DecisionSubjects(read.domain(), read.rules().symbols(),
                        read.rules().declarations(), read.rules().newtypes(),
                        Membership.built(add -> dependencies.forEach(add::add)));
        return new WhatAnAnswerTakesUp(subjects,
                new DecisionComparison(read.domain(), read.rules(), subjects));
    }

    /** Whether {@code comparison}, read under {@code reads}, is a column over an answer. */
    boolean comparison(StatedComparison comparison, InputReads reads) {
        return comparisons.readsOverAnAnswer(comparison, reads);
    }

    /**
     * Whether {@code part} of a condition, read under {@code reads}, is what a dependency answered
     * — whose truth is the column, however much of the input the call was asked about.
     */
    boolean part(Core part, InputReads reads) {
        return subjects.of(part, reads) instanceof DecisionSubject.AnAnswer;
    }
}
