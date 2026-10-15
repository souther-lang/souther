package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.ReadMeaning;
import souther.compiler.meaning.Proposition;

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
 * answer is, {@link DecisionSubjects} says; what a comparison states is the one statement every
 * reader of the condition takes ({@link WhatConditionsState}). The decision reading makes its
 * columns from the same two, so a condition the reading of the input hands over is one that
 * reading names. A reader that recognised calls to dependencies for itself would hand over
 * conditions the table holds no column for, and those would leave the account as read by nobody.
 *
 * <p>Only conditions over an answer. A truth of a position is a subject a row controls as well, and
 * it is the reading of the input's: a part of it that reading left unread is still unread.
 */
record WhatAnAnswerTakesUp(DecisionSubjects subjects) {

    /**
     * What the decision table over {@code read} takes up.
     *
     * <p>Which calls are answers a row stands in for is the environment's each is asked under
     * ({@link InputReads#standsIn}): a rule nothing stands a dependency in for, which is what a
     * declaration's clause is, is read where none is and has no answer in it a row controls.
     */
    static WhatAnAnswerTakesUp of(InputReading read) {
        ReadMeaning.WhereKept kept = KeptTruths.readIn(read);
        return new WhatAnAnswerTakesUp(new DecisionSubjects(read.domain(), read.rules().symbols(),
                read.rules().declarations(), read.rules().newtypes(), kept));
    }

    /**
     * Whether a comparison stating {@code stated} is a column over an answer: read to the end, and
     * about what a dependency answered somewhere in it.
     *
     * <p>Asked of what the comparison states and not of how it is spelled, so
     * {@code Decimal.compare(got, quota.value) >= 0} is taken up where {@code got >= quota.value}
     * is, and a comparison inside a lookup is taken up with what the lookup selects.
     *
     * <p>Read to the end, because the column is the statement. One part of which is over an answer
     * and another part of which nothing read is a condition nobody read; taken up for the part that
     * names an answer, the part nothing read would leave the account as read.
     */
    static boolean comparison(Proposition stated) {
        return !Proposition.leavesSomethingUnread(stated) && Proposition.aboutAnAnswer(stated);
    }

    /**
     * Whether {@code part} of a condition, read under {@code reads}, is the truth of what a
     * dependency answered — which is the column, however much of the input the call was asked
     * about.
     *
     * <p>Read the way the table reads a truth ({@link DecisionSubjects#truthOf}), so what is handed
     * over is what the table names: a part handed over on a reading of its own would be one both
     * sides let go. And only a truth: an answer that is a value inside what a part decides is not
     * what the part decides, and handing the part over for it would take an unread operation
     * around the answer with it.
     */
    boolean part(Core part, InputReads reads) {
        return subjects.isTheTruthOfAnAnswer(part, reads);
    }
}
