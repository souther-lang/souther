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

    /**
     * The conditions on the way here cannot all hold.
     *
     * <p>Which ones, and which way each of them goes, are marked where they are written rather than
     * listed here as line numbers. A condition is somewhere in the body, and where that is is what
     * the file is laid out as at the moment — so it is a caret for a renderer to place and not a
     * number for a report to carry.
     */
    record TheConditionsOnTheWayHereCannotAllHold() implements DeadBranchMessage, Supporting {}

    /** One of those conditions, on a way here that needs it to hold. */
    record ThisOneHoldsOnTheWayHere() implements DeadBranchMessage, Supporting {}

    /** One of those conditions, on a way here that needs it to fail. */
    record ThisOneFailsOnTheWayHere() implements DeadBranchMessage, Supporting {}

    /** An arm of a {@code match} on the way here, which the value it matched has to take. */
    record ThisArmIsTakenOnTheWayHere() implements DeadBranchMessage, Supporting {}

    /** An operator on the way here, which has to answer — an {@code Int} sum a run gets past is
     *  one whose value an {@code Int} holds. */
    record ThisHasToAnswerOnTheWayHere() implements DeadBranchMessage, Supporting {}

    /** The call that made the copy of {@code called} a mark of this proof stands in: the same place
     *  stands in the copy every other call of it makes, and this is the one the proof is about. */
    record ThisCallMadeTheCopyTheProofIsAbout(String called) implements DeadBranchMessage,
            Supporting {}

    /** The values it is written for are not values the position can hold. */
    record ThePositionStopsShortOfIt(String position, String admits) implements DeadBranchMessage,
            Supporting {}

    /** Every case the arm names is one the rules refuse where it is matched on. */
    record EveryCaseItIsWrittenForIsRefused(String position, String cases)
            implements DeadBranchMessage, Supporting {}

    /** The value matched on is one the source wrote, and never a case the arm names. */
    record TheValueMatchedOnIsNeverItsCase(String canBe, String cases)
            implements DeadBranchMessage, Supporting {}

    /** The position matched on is declared as cases none of which the arm is for. */
    record ItsDeclarationHoldsNoneOfTheCases(String position, String declared, String cases)
            implements DeadBranchMessage, Supporting {}

    /** The position matched on is declared as cases every one of which the arms before this one
     *  take. */
    record ItsDeclarationHoldsNothingTheArmsBeforeLeave(String position, String declared,
                                                        String cases)
            implements DeadBranchMessage, Supporting {}

    /** The arm is entered by one of several ways, and each of them is ruled out, as the notes after
     *  this one say. */
    record EveryWayInIsRuledOut() implements DeadBranchMessage, Supporting {}

    /** The branch is in a closure applied to the elements of containers nothing on the way here
     *  leaves one. */
    record ItsClosureIsAppliedToNothing(String containers) implements DeadBranchMessage,
            Supporting {}

    /**
     * A call on the way here applies a function to every element it is handed, and no run gets
     * past the application to the element at {@code index}, as the notes after this one say.
     *
     * <p>The notes are about that application and not about the function's body: what they mark
     * inside the function holds there on the application to that element.
     */
    record NoRunGetsPastOneOfItsApplications(int index) implements DeadBranchMessage,
            Supporting {}

    /** The call applying the function, on the way here. */
    record ThisAppliesAFunctionToEveryElement() implements DeadBranchMessage, Supporting {}

    /** What to do about it. */
    record TakeItOutOrLetSomethingReachIt() implements DeadBranchMessage, Supporting {}

    /** What to do about the departures of an attempted construction, none of which is taken:
     *  build the value outright. */
    record BuildTheValueRatherThanAttemptIt() implements DeadBranchMessage, Supporting {}

    /** What to do about one departure of an attempted construction where another is taken: it is
     *  written for its clause and stays, so it answers with {@code unreachable}. */
    record AnswerTheDepartureWithUnreachable() implements DeadBranchMessage, Supporting {}

    /** What to do about the success branch of an attempted construction that is never built:
     *  answer what it departs with rather than attempting it. */
    record AnswerTheDepartureRatherThanAttemptIt() implements DeadBranchMessage, Supporting {}
}
