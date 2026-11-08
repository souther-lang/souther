package souther.compiler.diag.msg;

/**
 * What the examples report says about a measure that has no number, and about what a reading could
 * not read.
 *
 * <p>A clause is a message of its own and a sentence carries it as a value: a line whose subject is
 * the measure opens with the family the reason is in ({@link NotApplicable}, {@link NotMeasured}),
 * and a line about something else says the clause alone. Each clause is a whole clause in every
 * language, so a sentence carrying one never assembles a translation out of English word order.
 */
public sealed interface ReasonMessage extends Message {

    // --- the two openings ---

    /** Nothing here was going to be measured, and nothing an author writes would change that. */
    record NotApplicable(Message clause) implements ReasonMessage, Prose {}

    /** Something could have been measured and was not, and the clause says what to do. */
    record NotMeasured(Message clause) implements ReasonMessage, Prose {}

    // --- nothing to be about ---

    record TheBehaviorHasNoBody() implements ReasonMessage, Prose {}

    record TheBodyOwesNoArm() implements ReasonMessage, Prose {}

    record TheOutputIsNotASum() implements ReasonMessage, Prose {}

    record TheRulesDrawNoLine() implements ReasonMessage, Prose {}

    record TheBehaviorIsMeasuredAtItsStages() implements ReasonMessage, Prose {}

    record ThePositionIsOneDataRatherThanASum() implements ReasonMessage, Prose {}

    record TheRulesLeaveTheInputNoValue() implements ReasonMessage, Prose {}

    record WhatItAnswersWithIsNotASum() implements ReasonMessage, Prose {}

    record TheRulesDivideNoPosition() implements ReasonMessage, Prose {}

    // --- never made ---

    record TheBuildDidNotAskForTheArms() implements ReasonMessage, Prose {}

    record NoRowNamesTheBehavior() implements ReasonMessage, Prose {}

    record ThisBuildDoesNotReadRows() implements ReasonMessage, Prose {}

    record TheBuildDidNotAskWhereTheRowsWent() implements ReasonMessage, Prose {}

    record NothingWasAskedFor() implements ReasonMessage, Prose {}

    record TheArmsWereNotAskedFor() implements ReasonMessage, Prose {}

    record TheBuildDidNotAskForARewrite() implements ReasonMessage, Prose {}

    // --- could not be finished ---

    record WhatArmsTheUnreadBodyHasIsUnknown() implements ReasonMessage, Prose {}

    record TheArmsCouldNotBeRead() implements ReasonMessage, Prose {}

    record WhatTheUnreadBodyCouldBeRewrittenAsIsUnknown() implements ReasonMessage, Prose {}

    record TheRowsCouldNotBeRunUnderARewrite() implements ReasonMessage, Prose {}

    record NothingCameBackFromTheRows() implements ReasonMessage, Prose {}

    record MoreCombinationsThanTheBuildCounts() implements ReasonMessage, Prose {}

    record NoRowCameBackToBeRead() implements ReasonMessage, Prose {}

    record TheRowsCarryNoAccountOfWhereTheyWent() implements ReasonMessage, Prose {}

    record TheBodyWasNotElaborated() implements ReasonMessage, Prose {}

    record NoRunThroughTheseRulesCanBeRecognised() implements ReasonMessage, Prose {}

    record NoLineWasDerivedAtAnyPosition() implements ReasonMessage, Prose {}

    record TheSignatureCouldNotBeRead() implements ReasonMessage, Prose {}

    record WhatTheBehaviorTakesWasNotRead() implements ReasonMessage, Prose {}

    record TheArmsCouldNotBeMeasured() implements ReasonMessage, Prose {}

    record ThePointsPlaceCouldNotBeRead() implements ReasonMessage, Prose {}

    record NotTiedToTheAuthorsLine() implements ReasonMessage, Prose {}

    record WhatLinesTheUnreadBodyDrawsIsUnknown() implements ReasonMessage, Prose {}

    record WhatTheUnreadBodyDividesIsUnknown() implements ReasonMessage, Prose {}

    record NoPartitionAxisWasDerivedAtAnyPosition() implements ReasonMessage, Prose {}
}
