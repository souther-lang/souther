package souther.compiler.diag.msg;

/**
 * The prose of a block {@code souther examples --generate} writes: the comments over and under the
 * rows, and the words a comment calls a thing a row is for.
 *
 * <p>Only the prose. A row, its values and the name it is given are source, and are the same
 * whichever language the comments around them are written in; the {@code //} a comment opens with
 * is the block's layout and not a word.
 */
public sealed interface GeneratedRowsMessage extends Message {

    // --- the block's heading ---

    record OneRowGenerated() implements GeneratedRowsMessage, Prose {}

    record RowsGenerated(int count) implements GeneratedRowsMessage, Prose {}

    record GeneratedBy() implements GeneratedRowsMessage, Prose {}

    record OneRowToFill() implements GeneratedRowsMessage, Prose {}

    record RowsToFill(int count) implements GeneratedRowsMessage, Prose {}

    record OneOptionalRow() implements GeneratedRowsMessage, Prose {}

    record OptionalRows(int count) implements GeneratedRowsMessage, Prose {}

    record ReplaceEachUnanswered(String unanswered) implements GeneratedRowsMessage, Prose {}

    record EnsuresWrittenFor(String behavior) implements GeneratedRowsMessage, Prose {}

    // --- over a row ---

    record SuggestedInput() implements GeneratedRowsMessage, Prose {}

    record Fills(String what) implements GeneratedRowsMessage, Prose {}

    record StopsAt(String what) implements GeneratedRowsMessage, Prose {}

    record Placed(Message words, String at) implements GeneratedRowsMessage, Prose {}

    record Quoted(Message words) implements GeneratedRowsMessage, Prose {}

    // --- what a thing a row is for is called ---

    record TheClassAt(String partition, String at) implements GeneratedRowsMessage, Prose {}

    record TheClassesWith(Message first, Message rest) implements GeneratedRowsMessage, Prose {}

    record ADecisionRule() implements GeneratedRowsMessage, Prose {}

    record ADecisionRuleOf(String behavior) implements GeneratedRowsMessage, Prose {}

    record ACombinationOfTheDecisions() implements GeneratedRowsMessage, Prose {}

    record ACombinationOfTheDecisionsOf(String behavior) implements GeneratedRowsMessage, Prose {}

    record TheLineAgainst(String line, String other) implements GeneratedRowsMessage, Prose {}

    record TheWeightOf(String position, String into) implements GeneratedRowsMessage, Prose {}

    record OrElse(String first, String rest) implements GeneratedRowsMessage, Prose {}

    record ASearchThatFindsItAtTheNode() implements GeneratedRowsMessage, Prose {}

    record ASearchThatFindsItBelowTheNode() implements GeneratedRowsMessage, Prose {}

    record ASearchThatFindsNothingAtALeaf() implements GeneratedRowsMessage, Prose {}

    record ASearchThatFindsNothingBelow() implements GeneratedRowsMessage, Prose {}

    record AKeyHeldTwiceThatHolds() implements GeneratedRowsMessage, Prose {}

    record AKeyHeldTwiceThatFails() implements GeneratedRowsMessage, Prose {}

    // --- under the block: what no row was written for ---

    record NoRowCanBeWrittenAtTheLine(String asked, String owedBy, Message noValue)
            implements GeneratedRowsMessage, Prose {}

    record NoRowFor(String subject, String behavior, Message said)
            implements GeneratedRowsMessage, Prose {}

    record NoRowForAnUnsearchedBehavior(String asked, String behavior)
            implements GeneratedRowsMessage, Prose {}

    record NoRowForOwedBy(String asked, String owedBy, Message why)
            implements GeneratedRowsMessage, Prose {}

    record NoRowForThe(Message what, String behavior, Message said)
            implements GeneratedRowsMessage, Prose {}

    record NothingOffersARowFor(Message what, String behavior, Message why)
            implements GeneratedRowsMessage, Prose {}

    record NothingAimsARowAt(Message what, String behavior, Message why)
            implements GeneratedRowsMessage, Prose {}

    record NoRowOfferedAnsweredElsewhere(Message what, String behavior)
            implements GeneratedRowsMessage, Prose {}

    record NoRowsOfferedAtAWithheldPosition(String axis) implements GeneratedRowsMessage, Prose {}

    record StoppedOneClassOrArmPastTheLimit(String behavior)
            implements GeneratedRowsMessage, Prose {}

    record StoppedClassesAndArmsPastTheLimit(String behavior, int count)
            implements GeneratedRowsMessage, Prose {}

    record OneGroupWasNotLookedIn(String behavior) implements GeneratedRowsMessage, Prose {}

    record GroupsWereNotLookedIn(int count, String behavior)
            implements GeneratedRowsMessage, Prose {}

    record StoppedWithNothingToBuildAgainst(String behavior)
            implements GeneratedRowsMessage, Prose {}

    record StoppedAsTheClassesWouldNotLink(String behavior)
            implements GeneratedRowsMessage, Prose {}

    record RowsOfferedWereNotRun(String behavior) implements GeneratedRowsMessage, Prose {}

    record StoppedAsRowsWereNotRead(String behavior, Message why)
            implements GeneratedRowsMessage, Prose {}

    // --- where a row stops ---

    record TheGuardAt(String at) implements GeneratedRowsMessage, Prose {}

    record TheGuardAtLookingFor(String at, String labels) implements GeneratedRowsMessage, Prose {}

    record LookingForWith(String first, String rest) implements GeneratedRowsMessage, Prose {}

    record WayPastIt(int way, Message came) implements GeneratedRowsMessage, Prose {}

    record NoRowWasFoundThatGoesPast(String guard, Message ways)
            implements GeneratedRowsMessage, Prose {}

    record ItsConditionNeverComesOutThatWay(String guard) implements GeneratedRowsMessage, Prose {}

    record TheWaysPastItCouldNotBeRead(String guard) implements GeneratedRowsMessage, Prose {}

    record NothingLooksPastOneGuardTwice(String guard) implements GeneratedRowsMessage, Prose {}

    record NothingWasLookedFor() implements GeneratedRowsMessage, Prose {}

    record NothingHoldsARowToIt() implements GeneratedRowsMessage, Prose {}

    record SoNoRowGoesThisWay(Message noValue) implements GeneratedRowsMessage, Prose {}

    record ItWouldRewriteAStatedValue() implements GeneratedRowsMessage, Prose {}

    record TheRowAlreadyDoesAllOfIt() implements GeneratedRowsMessage, Prose {}

    // --- what gave the offer no value ---

    record TheRuleAt(String rule, String at) implements GeneratedRowsMessage, Prose {}

    record WhatTheRulesAboutItLeave(String at) implements GeneratedRowsMessage, Prose {}

    record ComposingAValueFor(String at) implements GeneratedRowsMessage, Prose {}

    record GaveNothing(Message subject, Message why) implements GeneratedRowsMessage, Prose {}

    record GaveNoneAsUnread(Message why) implements GeneratedRowsMessage, Prose {}

    record GaveNoneForALargerMachine() implements GeneratedRowsMessage, Prose {}

    record GaveNoneHavingSpentTheComposing() implements GeneratedRowsMessage, Prose {}

    record GaveNoneHavingSpentThePattern() implements GeneratedRowsMessage, Prose {}

    // --- what a search that wrote no row came to ---

    record NothingCouldBuildARepresentative() implements GeneratedRowsMessage, Prose {}

    record EveryValueTriedWasRefused() implements GeneratedRowsMessage, Prose {}

    record EveryValueTriedWasRefusedOfSome() implements GeneratedRowsMessage, Prose {}

    record NothingCouldAnswerForADependency() implements GeneratedRowsMessage, Prose {}

    record ATableIsWhatThisNeeds() implements GeneratedRowsMessage, Prose {}

    record TheSearchLeftSomethingUntried() implements GeneratedRowsMessage, Prose {}

    record TheGroupWasNotOffered() implements GeneratedRowsMessage, Prose {}

    record NoRowComposedWasSeenReachingIt() implements GeneratedRowsMessage, Prose {}

    record TheWayInPlacesAtNoClass() implements GeneratedRowsMessage, Prose {}

    record TheBlockIsAsLongAsItMayBe() implements GeneratedRowsMessage, Prose {}

    record ItWouldNeedOnePositionToBeTwoThings(Message noValue)
            implements GeneratedRowsMessage, Prose {}

    record ItIsPastAConditionThatNeverComesOutSo(Message noValue)
            implements GeneratedRowsMessage, Prose {}

    record TheModulesClassesWereNotThere() implements GeneratedRowsMessage, Prose {}

    record ThisBuildComposedNoValues() implements GeneratedRowsMessage, Prose {}

    record TheGeneratedClassesWouldNotLink() implements GeneratedRowsMessage, Prose {}

    record ThePositionWasWithheld() implements GeneratedRowsMessage, Prose {}

    record TheRowsWereNotRead() implements GeneratedRowsMessage, Prose {}

    record NoCandidateWasOffered() implements GeneratedRowsMessage, Prose {}

    record NoReadingOfTheLineCouldBeSearched() implements GeneratedRowsMessage, Prose {}

    record EveryRowComposedReachesAnUnreachable() implements GeneratedRowsMessage, Prose {}
}
