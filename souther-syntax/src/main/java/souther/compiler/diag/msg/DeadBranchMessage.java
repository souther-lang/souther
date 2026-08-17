package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/**
 * What an author is told about a branch the model's own rules make dead.
 *
 * <p>The converse of {@link UnreachableMessage}, which is about an {@code unreachable} the rules
 * leave standing. Here the author wrote an ordinary branch and the rules rule it out.
 *
 * <p><b>The supporting arms are the proofs, one each.</b> This is the one place a proof is taken
 * apart: everything that decides anything reads the three answers and treats the proof as payload,
 * so a proof added later is a compile error here and a change to no policy.
 */
public sealed interface DeadBranchMessage extends Message {

    /** Nothing the model admits arrives at this branch, so no row can be written through it. */
    @Code(DiagnosticCode.E1327)
    record NothingReachesThisBranch() implements DeadBranchMessage, Reported {}

    /** The conditions on the way here cannot all hold. */
    record TheConditionsOnTheWayHereCannotAllHold(String conditions) implements DeadBranchMessage,
            Supporting {}

    /** The values it is written for are not values the position can hold. */
    record ThePositionStopsShortOfIt(String position, String admits) implements DeadBranchMessage,
            Supporting {}

    /** Every case the arm names is one the rules refuse where it is matched on. */
    record EveryCaseItIsWrittenForIsRefused(String position, String cases)
            implements DeadBranchMessage, Supporting {}

    /** What to do about it. */
    record TakeItOutOrLetSomethingReachIt() implements DeadBranchMessage, Supporting {}
}
