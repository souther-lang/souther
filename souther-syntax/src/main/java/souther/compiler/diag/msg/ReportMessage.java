package souther.compiler.diag.msg;

/**
 * The lines of the examples report a person reads, and the parts of those lines.
 *
 * <p>The marks a line opens with — {@code !}, {@code ·}, {@code ?}, {@code ~} — and how far it is
 * indented are the page's layout and not words, so they are not here. Everything a line says in
 * words is, and a part said inside several lines is a message of its own carried as a value.
 *
 * <p>A wording that turns on a value is two messages: a line about one row and a line about
 * several, a gap that was established and one nothing could decide. A part that a line may or may
 * not have is a message that may be {@link Nothing}, written with the punctuation that joins it to
 * what comes before, which is a question of the language and not of the page.
 */
public sealed interface ReportMessage extends Message {

    // --- joining ---

    /** A part a line does not have. */
    record Nothing() implements ReportMessage, Prose {}

    /** Two things said one after the other in a list. */
    record Listed(Message first, Message rest) implements ReportMessage, Prose {}

    /** Two things said together. */
    record Both(Message first, Message rest) implements ReportMessage, Prose {}

    /** Two reasons said one after the other. */
    record Reasons(Message first, Message rest) implements ReportMessage, Prose {}

    // --- the names of the measures ---

    record Signature() implements ReportMessage, Prose {}

    record Partition() implements ReportMessage, Prose {}

    record Combination() implements ReportMessage, Prose {}

    record Border() implements ReportMessage, Prose {}

    record Branch() implements ReportMessage, Prose {}

    record Decision() implements ReportMessage, Prose {}

    record Replacement() implements ReportMessage, Prose {}

    record Interaction() implements ReportMessage, Prose {}

    record Declarations() implements ReportMessage, Prose {}

    // --- a module, a behavior, and the page's last lines ---

    record ModuleMeasurement(Message status) implements ReportMessage, Prose {}

    record MeasurementComplete() implements ReportMessage, Prose {}

    record MeasurementPartial() implements ReportMessage, Prose {}

    record MeasurementUnavailable() implements ReportMessage, Prose {}

    record Implemented() implements ReportMessage, Prose {}

    record Unimplemented() implements ReportMessage, Prose {}

    record Injected() implements ReportMessage, Prose {}

    record RowsAndPending(String rows, String pending) implements ReportMessage, Prose {}

    record RowsNotRead() implements ReportMessage, Prose {}

    record Tally(Message behaviors, Message waiting) implements ReportMessage, Prose {}

    record OneBehaviorTallied(int implemented, int unimplemented, int injected)
            implements ReportMessage, Prose {}

    record BehaviorsTallied(int count, int implemented, int unimplemented, int injected)
            implements ReportMessage, Prose {}

    record OneRowWaitingForALet() implements ReportMessage, Prose {}

    record RowsWaitingForALet(int count) implements ReportMessage, Prose {}

    record AdequacyVerdict(Message verdict) implements ReportMessage, Prose {}

    record Satisfied() implements ReportMessage, Prose {}

    record NotSatisfied() implements ReportMessage, Prose {}

    record Undetermined() implements ReportMessage, Prose {}

    record WhatKeepsItOpen() implements ReportMessage, Prose {}

    record StoppedAtAFigureOfThisCompiler() implements ReportMessage, Prose {}

    record StoppedAtNoFigure() implements ReportMessage, Prose {}

    record OneGapMarked() implements ReportMessage, Prose {}

    record GapsMarked(int count) implements ReportMessage, Prose {}

    record OneRowDoesNotHold() implements ReportMessage, Prose {}

    record RowsDoNotHold(int count) implements ReportMessage, Prose {}

    record RowInSource(String behavior, String row, String source) implements ReportMessage, Prose {}

    record OneObligationRestsOnRowsThatDoNotHold() implements ReportMessage, Prose {}

    record ObligationsRestOnRowsThatDoNotHold(int count) implements ReportMessage, Prose {}

    // --- where a row that does not hold stopped ---

    record ItsInputCouldNotBeBuilt() implements ReportMessage, Prose {}

    record WhatItExpectsCouldNotBeBuilt() implements ReportMessage, Prose {}

    record ADependencyHadNoFakeForIt() implements ReportMessage, Prose {}

    record WhatItStatesBreaksWhatTheBehaviorEnsures() implements ReportMessage, Prose {}

    record ApplyingTheBehaviorGaveNoAnswer() implements ReportMessage, Prose {}

    record TheBehaviorAnsweredOtherwise() implements ReportMessage, Prose {}

    // --- the signature ---

    record OutputCases(String specified, String observed, String verified)
            implements ReportMessage, Prose {}

    record Partial() implements ReportMessage, Prose {}

    record NoRowExpects(String caseName) implements ReportMessage, Prose {}

    record UndecidedWhetherARowExpects(String caseName) implements ReportMessage, Prose {}

    record NoRowConfirms(String caseName) implements ReportMessage, Prose {}

    record UndecidedWhetherARowConfirms(String caseName) implements ReportMessage, Prose {}

    record InputCases(String input, String specified) implements ReportMessage, Prose {}

    record Excluded(int count) implements ReportMessage, Prose {}

    record NoRowUses(String caseName, Message premise) implements ReportMessage, Prose {}

    record UndecidedWhetherARowUses(String caseName, Message premise)
            implements ReportMessage, Prose {}

    record OnAPremise(String reasons) implements ReportMessage, Prose {}

    record DeclaredUnreachable(String caseName, Message because) implements ReportMessage, Prose {}

    record DeclaredUnreachableUnproven(String caseName, Message because, Message why)
            implements ReportMessage, Prose {}

    record DeclaredUnreachableAt(String caseName, String at, Message because)
            implements ReportMessage, Prose {}

    record DeclaredUnreachableAtUnproven(String caseName, String at, Message because, Message why)
            implements ReportMessage, Prose {}

    record BecauseOfOne(String reason) implements ReportMessage, Prose {}

    record OnEveryPath() implements ReportMessage, Prose {}

    // --- why a claim of the model is not proven here ---

    record ARuleAboutThePositionWentUnread() implements ReportMessage, Prose {}

    record TheRulesLeaveThePositionNoValue() implements ReportMessage, Prose {}

    record NothingWasReadAboutTheCase() implements ReportMessage, Prose {}

    record TheArmIsInsideAnother() implements ReportMessage, Prose {}

    record WhatTheRulesLeaveIsNotWhatIsHeld() implements ReportMessage, Prose {}

    // --- the partition ---

    record PartitionCounts(int axes, String partitions) implements ReportMessage, Prose {}

    record NotMeasuredHowMany(long count, Message clause) implements ReportMessage, Prose {}

    record NotAllOfItWasMeasured() implements ReportMessage, Prose {}

    record NoRowIsInPartition(String partition, String at, Message premise)
            implements ReportMessage, Prose {}

    record UndecidedWhetherARowIsInPartition(String partition, String at, Message premise)
            implements ReportMessage, Prose {}

    record OnlyARowThatDoesNotHoldIsInPartition(String partition, String at, String rows)
            implements ReportMessage, Prose {}

    record OnlyRowsThatDoNotHoldAreInPartition(String partition, String at, String rows)
            implements ReportMessage, Prose {}

    record NothingReadsThePosition(String position, int classes) implements ReportMessage, Prose {}

    record ReadWithoutTellingApart(String position, int classes) implements ReportMessage, Prose {}

    record NotToldApart(String position, int classes) implements ReportMessage, Prose {}

    record ToldApartInGroups(String position, int classes, int groups)
            implements ReportMessage, Prose {}

    record DividedBy(String position, String rules) implements ReportMessage, Prose {}

    // --- two classes together ---

    record ClassAt(String partition, String at) implements ReportMessage, Prose {}

    record With(String first, String second) implements ReportMessage, Prose {}

    record NoRowIsInCombination(String classes, Message premise) implements ReportMessage, Prose {}

    record UndecidedWhetherARowIsInCombination(String classes, Message premise)
            implements ReportMessage, Prose {}

    record OnlyARowThatDoesNotHoldIsInCombination(String classes, String rows)
            implements ReportMessage, Prose {}

    record OnlyRowsThatDoNotHoldAreInCombination(String classes, String rows)
            implements ReportMessage, Prose {}

    record Kept(String why) implements ReportMessage, Prose {}

    record PairsTooManyToEnumerate(int total) implements ReportMessage, Prose {}

    record PairsCounted(String pairs) implements ReportMessage, Prose {}

    record PairsCoveredAndUncovered(int covered, int uncovered) implements ReportMessage, Prose {}

    record PairsCoveredAndUncoveredOfTheRowsRead(int covered, int uncovered)
            implements ReportMessage, Prose {}

    // --- the border ---

    record BorderCounts(int borders, String obligations) implements ReportMessage, Prose {}

    record Refuted(int count) implements ReportMessage, Prose {}

    record NoRowTellsApart(String line, String other, Message would)
            implements ReportMessage, Prose {}

    record ARowAtWould(String input) implements ReportMessage, Prose {}

    record NoRowFixesTheWeight(String position, String into) implements ReportMessage, Prose {}

    /** A point of a line some rule drew, by its role, which side of the line, and the rule. */
    record PointOfALine(String role, Message side, String rule) implements ReportMessage, Prose {}

    /** A point of a declaration's line, said on the quantity the declaration wrote. */
    record DeclaredPointAt(String role, Message side, String said, String rule)
            implements ReportMessage, Prose {}

    /** A point of a declaration's line that has no quantity in the declaration's words. */
    record DeclaredPointOf(String role, String rule) implements ReportMessage, Prose {}

    /** No row at a point that is one value. */
    record NoRowIsAtThe(Message point) implements ReportMessage, Prose {}

    /** No row at a point that is a run of values. */
    record NoRowIsAtAn(Message point) implements ReportMessage, Prose {}

    record OnlyARowThatDoesNotHoldIsAtThe(Message point, String rows)
            implements ReportMessage, Prose {}

    record OnlyARowThatDoesNotHoldIsAtAn(Message point, String rows)
            implements ReportMessage, Prose {}

    record OnlyRowsThatDoNotHoldAreAtThe(Message point, String rows)
            implements ReportMessage, Prose {}

    record OnlyRowsThatDoNotHoldAreAtAn(Message point, String rows)
            implements ReportMessage, Prose {}

    record NoRowCanStandAt(Message point, Message why) implements ReportMessage, Prose {}

    record ThePointIsAnsweredNotAtEveryReading(String role, String rule)
            implements ReportMessage, Prose {}

    record NoPointIsOwed(String role, Message side, String line, String rule, Message why)
            implements ReportMessage, Prose {}

    record NoPointOfTheRuleIsOwed(String role, Message side, String rule, Message why)
            implements ReportMessage, Prose {}

    record NoPointExists(String role, String line, String rule, Message why)
            implements ReportMessage, Prose {}

    record NoPointOfTheRuleExists(String role, String rule, Message why)
            implements ReportMessage, Prose {}

    record TheClassAtTheLineHoldsOneValue() implements ReportMessage, Prose {}

    record ExcludedBecause(Message why) implements ReportMessage, Prose {}

    record TheOrderNamesNoValueThere() implements ReportMessage, Prose {}

    record ReadAs(String at, String asks, String calls, String beside, Message bound)
            implements ReportMessage, Prose {}

    record MoreReadings(int count) implements ReportMessage, Prose {}

    record TheBoundWrittenIs(String level, Message heldIn) implements ReportMessage, Prose {}

    record TheBoundIsReadOutOf(String data) implements ReportMessage, Prose {}

    // --- no value can ---

    record NoValueCanStandThere() implements ReportMessage, Prose {}

    record NoValueCanStandAtIt() implements ReportMessage, Prose {}

    record NoValueCanStandHere() implements ReportMessage, Prose {}

    record NoValueCanStandAt(String where) implements ReportMessage, Prose {}

    record NoValueCanGoThatWay() implements ReportMessage, Prose {}

    record NoValueCanReachThatArm() implements ReportMessage, Prose {}

    record NoValueCanReachItComingOutSo() implements ReportMessage, Prose {}

    // --- a rule, and a point of its line ---

    record ReachedRule(String kind, String by, String at) implements ReportMessage, Prose {}

    record RuleOutOfSight(String kind, String by) implements ReportMessage, Prose {}

    // --- the calls a copy of a helper was made at ---

    record InCopies(String calls) implements ReportMessage, Prose {}

    record CallInside(String inner, Message outer) implements ReportMessage, Prose {}

    record CallWithNoPlace(String name, String step) implements ReportMessage, Prose {}

    record InCalls(Message calls) implements ReportMessage, Prose {}

    record PlaceInCalls(Message place, Message calls) implements ReportMessage, Prose {}

    record WhatInCalls(Message what, Message calls) implements ReportMessage, Prose {}

    // --- more joining ---

    /** A part that is code or a name, said as it is written and in no language's words. */
    record Verbatim(String said) implements ReportMessage, Prose {}

    /** Where else a point of a declaration's line was settled, said after the line. */
    record SettledElsewhere(Message where) implements ReportMessage, Prose {}

    /** Two places a point was settled at besides its line. */
    record SettledAtBoth(Message first, Message rest) implements ReportMessage, Prose {}

    /** A place the values stop at, on the declaration's own quantity. */
    record WhereTheValuesStopAt(String at) implements ReportMessage, Prose {}

    /** A line a point was settled up to. */
    record UpToTheLine(Message line) implements ReportMessage, Prose {}

    /** A rule, and what was asked of it that nothing answered. */
    record RuleThenAsked(String rule, Message asked) implements ReportMessage, Prose {}

    /** What a search met of this compiler's, said before what the search came back with. */
    record MetFirst(Message met, Message rest) implements ReportMessage, Prose {}

    /** One thing said, and another true beside it. */
    record Also(Message first, Message rest) implements ReportMessage, Prose {}

    record AndAlso(Message first, Message rest) implements ReportMessage, Prose {}

    record AndThen(String said) implements ReportMessage, Prose {}

    /** Either of two things. */
    record Either(Message first, Message rest) implements ReportMessage, Prose {}

    record Then(Message first, Message rest) implements ReportMessage, Prose {}

    record ThenAfter(String first, String rest) implements ReportMessage, Prose {}

    record PartsOfOne(Message first, Message rest) implements ReportMessage, Prose {}

    record Bracketed(Message inner) implements ReportMessage, Prose {}

    // --- where a point is, and the names of the measures a subject is of ---

    record AtTheLine() implements ReportMessage, Prose {}

    record BesideTheLine() implements ReportMessage, Prose {}

    record InTheRegion() implements ReportMessage, Prose {}

    record SideAbove() implements ReportMessage, Prose {}

    record SideBelow() implements ReportMessage, Prose {}

    record PlacedOn(Message where) implements ReportMessage, Prose {}

    record PlacedOnASide(Message where, Message side) implements ReportMessage, Prose {}

    record MeasureReading() implements ReportMessage, Prose {}

    record MeasureBoundary() implements ReportMessage, Prose {}

    // --- what keeps the verdict open ---

    record SubjectModule(String module) implements ReportMessage, Prose {}

    record SubjectSource(String source) implements ReportMessage, Prose {}

    record SubjectNamedRow(String name, String behavior) implements ReportMessage, Prose {}

    record SubjectUnnamedRow(String row, String behavior) implements ReportMessage, Prose {}

    record SubjectInput(String input, String behavior) implements ReportMessage, Prose {}

    record SubjectRule(String rule, String at, String why) implements ReportMessage, Prose {}

    record SubjectFork(String module) implements ReportMessage, Prose {}

    record SubjectArm(String definition) implements ReportMessage, Prose {}

    record SubjectMeasure(Message measure, String behavior) implements ReportMessage, Prose {}

    record SubjectAxis(String term, String behavior) implements ReportMessage, Prose {}

    record SubjectRewrite(String behavior, String rewrite) implements ReportMessage, Prose {}

    record ItStoppedAtAsWell(Message next, String figures) implements ReportMessage, Prose {}

    record WriteEachCaseOut(String rows) implements ReportMessage, Prose {}

    record StoppedAtWhichNoOptionSets(String figures) implements ReportMessage, Prose {}

    record TheSearchStoppedAt(String figures) implements ReportMessage, Prose {}

    record StoppedBeforeARowThatTellsTheRewriteApart(String figures)
            implements ReportMessage, Prose {}

    record ReadTheRule() implements ReportMessage, Prose {}

    record ReadWhatTheMeasureWentWithout() implements ReportMessage, Prose {}

    record ReadWhatWasTried() implements ReportMessage, Prose {}

    record ReadTheFork() implements ReportMessage, Prose {}

    record ReadThisCompilersProof() implements ReportMessage, Prose {}

    record WeighWhatToTellApart() implements ReportMessage, Prose {}

    record NothingToDo() implements ReportMessage, Prose {}

    // --- a figure of this compiler's ---

    record FigureSaid(Message counts, String name, String most) implements ReportMessage, Prose {}

    record StoppedAt(Message figures) implements ReportMessage, Prose {}

    record AndAt(Message first, Message rest) implements ReportMessage, Prose {}

    // --- a rule nothing read, a position nothing divided ---

    record DividedNoWay(String position) implements ReportMessage, Prose {}

    record RuleNotRead(String rule, Message why, Message stopped, String at, String calls,
                       Message sentTo) implements ReportMessage, Prose {}

    record RuleDrawsNoLine(String rule, Message why, Message stopped, String at, String calls,
                           Message sentTo) implements ReportMessage, Prose {}

    record SentTo(String at) implements ReportMessage, Prose {}

    record MayStopARun(String rule, Message every, String calls) implements ReportMessage, Prose {}

    record EveryRunStops(String stops) implements ReportMessage, Prose {}

    record StopsIn(String operation, String where) implements ReportMessage, Prose {}

    record ItIs(String form, String value) implements ReportMessage, Prose {}

    record ItIsFromTo(String form, String least, String greatest)
            implements ReportMessage, Prose {}

    record ItIsAtLeast(String form, String least) implements ReportMessage, Prose {}

    record ItIsAtMost(String form, String greatest) implements ReportMessage, Prose {}

    record CaseExpansion(String rule, String line, String cutAt, String arms, int ordinal, int of,
                         String calls, String cameTo) implements ReportMessage, Prose {}

    record PositionNotRead(String at, Message why, Message stopped)
            implements ReportMessage, Prose {}

    record RulesNotReached(String at) implements ReportMessage, Prose {}

    record TheDecisionWentWithout(String rule, String entry) implements ReportMessage, Prose {}

    record NotAccountedFor(String rule, Message asked, String calls, String stops,
                           Message shortOf) implements ReportMessage, Prose {}

    record AndTheAnswerAtItsPosition(Message why) implements ReportMessage, Prose {}

    record TheImageIsNotShown(String names) implements ReportMessage, Prose {}

    record NoRowShownComputedIn(String numbers) implements ReportMessage, Prose {}

    record AtLeast(String at) implements ReportMessage, Prose {}

    record Above(String at) implements ReportMessage, Prose {}

    record AtMost(String at) implements ReportMessage, Prose {}

    record Below(String at) implements ReportMessage, Prose {}

    record OfAnySize() implements ReportMessage, Prose {}

    // --- what a rule left open ---

    record WhichValuesMayStandAt(String subject) implements ReportMessage, Prose {}

    record WhereTheValuesStopOn(String subject) implements ReportMessage, Prose {}

    record WhetherTheValuesStopOn(String subject) implements ReportMessage, Prose {}

    record WhatThisRuleStatesAbout(String subject) implements ReportMessage, Prose {}

    record WhichClassSomeValuesAreIn(String subject) implements ReportMessage, Prose {}

    // --- why a rule drew no line, or was not read ---

    record WrittenInAFormNotRead() implements ReportMessage, Prose {}

    record LeftOpenByAnUnreadAlternative() implements ReportMessage, Prose {}

    record TheValuesLeftAreMoreThanWorkedOut() implements ReportMessage, Prose {}

    record WhatTheRulesTellApartIsMoreThanWorkedOut() implements ReportMessage, Prose {}

    record ComparedAgainstValuesNoLineIsDrawnOn() implements ReportMessage, Prose {}

    record TheLineFallsAtAnInexactNumber() implements ReportMessage, Prose {}

    record AValueBesideTheLineIsNotWritten() implements ReportMessage, Prose {}

    record HowTheCasePositionsPairIsUnknown() implements ReportMessage, Prose {}

    record SeveralLinesHeldTogether() implements ReportMessage, Prose {}

    record ARelationNotShownToReachEveryValue() implements ReportMessage, Prose {}

    record ARelationNotShownReachedFromEveryValue() implements ReportMessage, Prose {}

    record ARelationShownOverARegion() implements ReportMessage, Prose {}

    record ItRelatesTwoValues() implements ReportMessage, Prose {}

    record ItRelatesTheElements() implements ReportMessage, Prose {}

    record ItIsAboutWhatTheValuesComeTo() implements ReportMessage, Prose {}

    record ItIsAboutARemainder() implements ReportMessage, Prose {}

    record ItComparesWhatARunWorksOut() implements ReportMessage, Prose {}

    record ItRestrictsThePosition() implements ReportMessage, Prose {}

    record ItIsAboutADerivedValue() implements ReportMessage, Prose {}

    record ItIsAboutAnElementOfOneOfSeveral() implements ReportMessage, Prose {}

    record ItCutsNothing() implements ReportMessage, Prose {}

    record EveryRunReachingItStops() implements ReportMessage, Prose {}

    record EveryValueComesOutOneSide() implements ReportMessage, Prose {}

    record TheClassesAreNotOneList() implements ReportMessage, Prose {}

    record ItCutsOutsideWhatTheQuantityHolds() implements ReportMessage, Prose {}

    record NoRowArrivesAtItsLine() implements ReportMessage, Prose {}

    record NoRowArrivesAtTheRelation() implements ReportMessage, Prose {}

    record ItNeverTurnsOnThisLine() implements ReportMessage, Prose {}

    record APartOfItWasNotRead() implements ReportMessage, Prose {}

    record ItComparesAProductOfTwoValues() implements ReportMessage, Prose {}

    record ItComparesAQuotientByAValue() implements ReportMessage, Prose {}

    record ItComparesARemainderByAValue() implements ReportMessage, Prose {}

    record TheRulesWereNotReached() implements ReportMessage, Prose {}

    record ItsTypeWasNotWorkedOut() implements ReportMessage, Prose {}

    // --- the branch ---

    record ARowWentThroughAnArmProvenUnreached() implements ReportMessage, Prose {}

    record WhichRuleDecidesTheForkIsUnknown(String fork, String from)
            implements ReportMessage, Prose {}

    record UndecidedWhetherARowGoesThrough(String arm, String at, Message premise)
            implements ReportMessage, Prose {}

    record NoRowGoesThrough(String arm, String at) implements ReportMessage, Prose {}

    record OnlyARowThatDoesNotHoldGoesThrough(String arm, String at, String rows)
            implements ReportMessage, Prose {}

    record OnlyRowsThatDoNotHoldGoThrough(String arm, String at, String rows)
            implements ReportMessage, Prose {}

    // --- why a combination was kept ---

    record TheFunctionWasReadAsAWhole(String at, String shortfalls)
            implements ReportMessage, Prose {}

    record WhatTheWayReadsTogetherWasNotRead(Message cause) implements ReportMessage, Prose {}

    record ADecisionNothingNames() implements ReportMessage, Prose {}

    record ARuleNoDecisionReads(String at) implements ReportMessage, Prose {}

    record SomethingElseAppliesIt() implements ReportMessage, Prose {}

    record ItAppliesToEveryElement(String operation) implements ReportMessage, Prose {}

    record ItAppliesUntilOneHolds(String operation) implements ReportMessage, Prose {}

    record ItAppliesUntilOneFails(String operation) implements ReportMessage, Prose {}

    record ItAppliesToOneAtMost(String operation) implements ReportMessage, Prose {}

    record ItAppliesToSome(String operation) implements ReportMessage, Prose {}

    record ItAppliesOverNoPosition(String operation) implements ReportMessage, Prose {}

    record AWayGoesToAForkNoPositionNames() implements ReportMessage, Prose {}

    record TheWaysCouldNotAllBeWrittenDown() implements ReportMessage, Prose {}

    record AWayGoesToAnArmWhoseWaysAreNotToldApart() implements ReportMessage, Prose {}

    record AForkHasMoreWaysInThanAreRead() implements ReportMessage, Prose {}

    record AWayRunsInsideAFunctionValue() implements ReportMessage, Prose {}

    record AWayIsTakenByAnAttempt() implements ReportMessage, Prose {}

    // --- the replacement ---

    record LeftOpen(long count) implements ReportMessage, Prose {}

    record NoRowWouldComeOutDifferently(String rewrite) implements ReportMessage, Prose {}

    record NotDecidedWhetherARowWouldComeOutDifferently(String rewrite)
            implements ReportMessage, Prose {}

    record AnArmAnsweredAs(String arm, String at, String as) implements ReportMessage, Prose {}

    record AnArmOutOfSightAnsweredAs(String arm, String as, Message where)
            implements ReportMessage, Prose {}

    record TheBodyAlwaysAnswered(Message row) implements ReportMessage, Prose {}

    record TheFoldAt(String at, Message walked) implements ReportMessage, Prose {}

    record TheFoldOutOfSight(Message where, Message walked) implements ReportMessage, Prose {}

    record InAForkOutOfSight(String definition) implements ReportMessage, Prose {}

    record InADefinitionOutOfSight(String definition) implements ReportMessage, Prose {}

    record AtTheConstruct(String construct) implements ReportMessage, Prose {}

    record Lowered(String lowered) implements ReportMessage, Prose {}

    record ArmAs(String part, String with) implements ReportMessage, Prose {}

    record StoppedAfterItsFirstElement() implements ReportMessage, Prose {}

    record HandedEachStepTheSeed() implements ReportMessage, Prose {}

    record AnArmAnsweringAs(String arm, String as) implements ReportMessage, Prose {}

    record TheBodyAnsweringWhatARowAnswers(Message row) implements ReportMessage, Prose {}

    record TheFoldStoppingAfterItsFirstElement() implements ReportMessage, Prose {}

    record EachStepOfTheFoldHandedTheSeed() implements ReportMessage, Prose {}

    // --- the combinations of decisions ---

    record MeetingsNotWalked(int count) implements ReportMessage, Prose {}

    record InteractionCombinations(String combinations) implements ReportMessage, Prose {}

    record InteractionCombinationsUncounted(int count, Message why)
            implements ReportMessage, Prose {}

    record NoRowMakesThisCombination(Message premise) implements ReportMessage, Prose {}

    record UndecidedWhetherARowMakesThisCombination(Message premise)
            implements ReportMessage, Prose {}

    record NoRowMakesAnyOfTheseCombinations(int count, Message premise)
            implements ReportMessage, Prose {}

    record UndecidedWhetherARowMakesAnyOfThese(int count, Message premise)
            implements ReportMessage, Prose {}

    record OnlyARowThatDoesNotHoldMakesThisCombination(String rows)
            implements ReportMessage, Prose {}

    record OnlyRowsThatDoNotHoldMakeThisCombination(String rows) implements ReportMessage, Prose {}

    record DecidedTogether() implements ReportMessage, Prose {}

    record Under(String condition) implements ReportMessage, Prose {}

    record WaysEither() implements ReportMessage, Prose {}

    record WaysOr() implements ReportMessage, Prose {}

    // --- the decision ---

    record DecisionNotFullyRead() implements ReportMessage, Prose {}

    record DecisionCounts(int rules, int taken) implements ReportMessage, Prose {}

    record DecisionCountsUntaken(int rules, Message why) implements ReportMessage, Prose {}

    record NoRowTakesADecisionRule(Message premise) implements ReportMessage, Prose {}

    record UndecidedWhetherARowTakesADecisionRule(Message premise)
            implements ReportMessage, Prose {}

    record OnlyARowThatDoesNotHoldTakesADecisionRule(String rows)
            implements ReportMessage, Prose {}

    record OnlyRowsThatDoNotHoldTakeADecisionRule(String rows) implements ReportMessage, Prose {}

    record NothingCouldShowARowAtADecisionRule(Message cameTo) implements ReportMessage, Prose {}

    record NotComposedAgainst(String what) implements ReportMessage, Prose {}

    record NoInputTakesOneWay() implements ReportMessage, Prose {}

    record NoInputTakesTheseWays(int count) implements ReportMessage, Prose {}

    record TheConditionsClash() implements ReportMessage, Prose {}

    record TheNumbersLeaveNone() implements ReportMessage, Prose {}

    record NoRowIsOwedAtOneRule() implements ReportMessage, Prose {}

    record NoRowIsOwedAtTheseRules(int count) implements ReportMessage, Prose {}

    record AComposedRowWentElsewhere() implements ReportMessage, Prose {}

    record AComposedRowWasShortOfTheWay() implements ReportMessage, Prose {}

    record EveryRuleTurnsOnSomethingUnrecorded() implements ReportMessage, Prose {}

    record NoRuleTheRunDidAllOf() implements ReportMessage, Prose {}

    record AConditionCameOutBothWays() implements ReportMessage, Prose {}

    record ItWasPlacedAtMoreThanOneRule() implements ReportMessage, Prose {}

    record ItWentDownAWayNoInputTakes() implements ReportMessage, Prose {}

    record NothingWatchedTheRow() implements ReportMessage, Prose {}

    record ItsWayNeedsOnePositionToBeTwoThings(Message noValue) implements ReportMessage, Prose {}

    record ItsWayGoesThroughAnArmNothingReaches(Message noValue)
            implements ReportMessage, Prose {}

    record ItsWayNeedsAComparisonToComeOutOneWay(Message noValue)
            implements ReportMessage, Prose {}

    record ItsWayGoesPastAConditionThatNeverComesOutSo(Message noValue)
            implements ReportMessage, Prose {}

    record TheNumbersOnItsWayLeaveNoValue(Message noValue) implements ReportMessage, Prose {}

    record TheComparisonHolds(String at) implements ReportMessage, Prose {}

    record TheComparisonDoesNotHold(String at) implements ReportMessage, Prose {}

    record TheComparisonHoldsOnItsEvaluation(String at, Message ordinal)
            implements ReportMessage, Prose {}

    record TheComparisonDoesNotHoldOnItsEvaluation(String at, Message ordinal)
            implements ReportMessage, Prose {}

    record FirstOrdinal(int count) implements ReportMessage, Prose {}

    record SecondOrdinal(int count) implements ReportMessage, Prose {}

    record ThirdOrdinal(int count) implements ReportMessage, Prose {}

    record NthOrdinal(int count) implements ReportMessage, Prose {}

    record TheOperationAnswersTrue(String at) implements ReportMessage, Prose {}

    record TheOperationAnswersFalse(String at) implements ReportMessage, Prose {}

    record ItGoesThrough(String arm, String at) implements ReportMessage, Prose {}

    record AConditionWithNowhereToSendYou() implements ReportMessage, Prose {}

    // --- an obligation nothing decided ---

    record UndecidedWhetherARowIsAt(Message point, Message met) implements ReportMessage, Prose {}

    record UndecidedBecauseNothingWasRead(Message point, Message why)
            implements ReportMessage, Prose {}

    record NothingCouldShowARowCanBeWrittenAt(Message point, String why)
            implements ReportMessage, Prose {}

    record NoSearchEstablishedARowAt(Message point) implements ReportMessage, Prose {}

    record ARunMayStopOnTheWayTo(Message point, String stops) implements ReportMessage, Prose {}

    record EveryRowThereReachesAnUnreachable(Message point, String reasons)
            implements ReportMessage, Prose {}

    record TheReadingsRanPastTheLimit() implements ReportMessage, Prose {}

    record AnOperator() implements ReportMessage, Prose {}

    record ACall() implements ReportMessage, Prose {}

    record AConstruction() implements ReportMessage, Prose {}

    record TheWalkReachedNoValue() implements ReportMessage, Prose {}

    record TheWalkCouldNotBeTaken() implements ReportMessage, Prose {}

    record NoRowCameBackToReadThere() implements ReportMessage, Prose {}

    record TheKeysCouldNotBeToldApart() implements ReportMessage, Prose {}

    record WhetherTheRunGotToTheRuleTurnsOn(Message on) implements ReportMessage, Prose {}

    record APartOfTheWayNotRead() implements ReportMessage, Prose {}

    record APartTakingMoreReadingsThanAreMade() implements ReportMessage, Prose {}

    record APartTakingMoreReadingsInAllThanAreMade() implements ReportMessage, Prose {}

    record APartComingToMorePartsThanAreConcluded() implements ReportMessage, Prose {}

    record APartOverMoreWaysThanAreWrittenOut() implements ReportMessage, Prose {}

    record APartAboutALargerContainer() implements ReportMessage, Prose {}

    record SomethingTheRowDoesNotWrite() implements ReportMessage, Prose {}

    record WhichApplicationBelongsToTheElement() implements ReportMessage, Prose {}

    record ANumberThisHostHadNoRoomFor() implements ReportMessage, Prose {}

    record ANumberThisCompilerCannotHold() implements ReportMessage, Prose {}

    record WhichCaseIsNotWorkedOut() implements ReportMessage, Prose {}

    record ARowWasBuiltForIt(String causes) implements ReportMessage, Prose {}

    record NothingHereSettledIt(Message budgets, Message populations, Message capacities)
            implements ReportMessage, Prose {}

    record AFigureIsWhy(String budgets) implements ReportMessage, Prose {}

    record ThisCompilerWritesSomeOf(String populations) implements ReportMessage, Prose {}

    record ThisCompilerCouldNotHold(String capacities) implements ReportMessage, Prose {}

    record TheObservationWasStoppedByALimit() implements ReportMessage, Prose {}

    record NothingCouldReadItBack() implements ReportMessage, Prose {}

    // --- what a search at a point came to ---

    record ThisCompilerStoppedAt(String budgets, Message populations, Message capacities,
                                 String why, Message leftOut) implements ReportMessage, Prose {}

    record ThisCompilerLeftUntried(String untried, String why, Message leftOut)
            implements ReportMessage, Prose {}

    record OverLessThanThePointHad(String budgets, Message populations, Message capacities,
                                   String why, Message leftOut) implements ReportMessage, Prose {}

    record NothingWasPlannedForIt(String budgets, Message leftOut)
            implements ReportMessage, Prose {}

    record NothingComposedOne(String why) implements ReportMessage, Prose {}

    record AlsoLeftOut(String said) implements ReportMessage, Prose {}

    record NotEveryConditionOnTheWayToTheLine(Message conditions)
            implements ReportMessage, Prose {}

    record NotEveryConditionOnTheWayToTheRule(Message conditions)
            implements ReportMessage, Prose {}

    record WhyLeftOutAt(Message why, Message where) implements ReportMessage, Prose {}

    record WritesSomeOf(Message populations) implements ReportMessage, Prose {}

    record CouldNotHold(Message capacities) implements ReportMessage, Prose {}

    record AndWritesSomeOf(String populations) implements ReportMessage, Prose {}

    record AndCouldNotHold(String capacities) implements ReportMessage, Prose {}

    // --- a condition a composing went without ---

    record AComparisonOverMoreThanOneAnswer() implements ReportMessage, Prose {}

    record APlaceOnTheAnswersOwnOrder() implements ReportMessage, Prose {}

    record AStatementAboutSeveralAnswers() implements ReportMessage, Prose {}

    record AComparisonInsideAnAnswerOnNoOrder() implements ReportMessage, Prose {}

    record AConditionInsideAnAnswerWithNoValue() implements ReportMessage, Prose {}

    record AConditionOnADependencyWithNoValue() implements ReportMessage, Prose {}

    record AConditionOnADependencyAndANumber(Message budgets) implements ReportMessage, Prose {}

    record AConditionInsideAnAnswerOverMoreWays(Message budgets)
            implements ReportMessage, Prose {}

    record AConditionOnOneCall() implements ReportMessage, Prose {}

    record AConditionOnAWayThatLeavesNothing() implements ReportMessage, Prose {}

    record LookedForAlongTheWholeWay(Message budgets) implements ReportMessage, Prose {}

    record AConditionOnPositionsWithNoValue() implements ReportMessage, Prose {}

    record AnotherNumberWhereTheRowIsWritten() implements ReportMessage, Prose {}

    record ElementsWrittenAlike() implements ReportMessage, Prose {}

    record AConditionTheRunDecides(Message what, Message past) implements ReportMessage, Prose {}

    record AValueTheBodyWorksOut() implements ReportMessage, Prose {}

    record WhatAnOperationAnswers() implements ReportMessage, Prose {}

    record ACountOfElements() implements ReportMessage, Prose {}

    record ACountAgainstANumberNotHeld() implements ReportMessage, Prose {}

    record ACountWithinAnElement() implements ReportMessage, Prose {}

    record ANumberOverElements() implements ReportMessage, Prose {}

    record ARemainderOfAForm() implements ReportMessage, Prose {}

    record ARemainderByAnInput() implements ReportMessage, Prose {}

    record AProductOfTwoNumbers() implements ReportMessage, Prose {}

    record TwoValuesBeingOne() implements ReportMessage, Prose {}

    record AStringInALanguage() implements ReportMessage, Prose {}

    record AStringInsideAnother() implements ReportMessage, Prose {}

    record AnOrderOfNoOnePosition() implements ReportMessage, Prose {}

    record MadeFromWhatTheReadingStoppedAt(Message reasons) implements ReportMessage, Prose {}

    record PositionsThisCompilerStoppedLookingAt(Message stopped)
            implements ReportMessage, Prose {}

    // --- why a condition on the way was not taken in ---

    record AQuantityOnNoOrder() implements ReportMessage, Prose {}

    record APathKnowsNoAlternatives() implements ReportMessage, Prose {}

    record AnAnswerARowStandsIn() implements ReportMessage, Prose {}

    record ANodeBelowWhatARowWrites() implements ReportMessage, Prose {}

    record AnotherElementThanTheWayHolds() implements ReportMessage, Prose {}

    record APlaceThePathDoesNotRead() implements ReportMessage, Prose {}

    record APathKnowsNoCaseAValueIsNot() implements ReportMessage, Prose {}

    record APathKnowsNoSamenessOfValues() implements ReportMessage, Prose {}

    record APathKnowsNoStringInsideAnother() implements ReportMessage, Prose {}

    record APathKnowsNoPlaceOnAnOrder() implements ReportMessage, Prose {}

    record APathKnowsNoCountOfElements() implements ReportMessage, Prose {}

    record APathKnowsNoNumberOverElements() implements ReportMessage, Prose {}

    record APathHoldsElementFactsAsWritten() implements ReportMessage, Prose {}

    record ANumberThePathCannotHold() implements ReportMessage, Prose {}

    record MoreWaysThanAreTaken() implements ReportMessage, Prose {}

    record MoreAlternativesThanAreTried(Message figure) implements ReportMessage, Prose {}

    record MoreChoicesThanAreWrittenOut(Message figure) implements ReportMessage, Prose {}

    // --- why the meaning of a condition was not read ---

    record AContainerAtNoPosition() implements ReportMessage, Prose {}

    record AValueAtNoPosition() implements ReportMessage, Prose {}

    record AStringOfNoInput() implements ReportMessage, Prose {}

    record AnArmNotReadAsANarrowing() implements ReportMessage, Prose {}

    record NeitherAComparisonNorACombination() implements ReportMessage, Prose {}

    record HowManyAContainerHolds() implements ReportMessage, Prose {}

    record AProductOfNonConstants() implements ReportMessage, Prose {}

    record AQuotientByANonConstant() implements ReportMessage, Prose {}

    record ARemainderByANonConstant() implements ReportMessage, Prose {}

    record SomethingThatIsNoArithmetic() implements ReportMessage, Prose {}

    record ANumberTooLargeToHold() implements ReportMessage, Prose {}

    record AQuotientByNought() implements ReportMessage, Prose {}

    record WhatItAnswersHasNoForm(String operation) implements ReportMessage, Prose {}

    record ANumberOfWhatItAnswersHasNoLaw(String measure, String madeBy)
            implements ReportMessage, Prose {}

    record ADateMovedByMonths(String operation) implements ReportMessage, Prose {}

    record APartOfADateMovedByMonths(String measure, String madeBy)
            implements ReportMessage, Prose {}

    record CodePointsOfWhatItAnswers(String madeBy) implements ReportMessage, Prose {}

    record TwoElementsOfOneContainer() implements ReportMessage, Prose {}

    record ItsDeclarationGivesItNoSuchSide(String operation) implements ReportMessage, Prose {}

    record ItsLawIsNotProvedOfItsBody(String operation) implements ReportMessage, Prose {}

    record WhatARecursiveHelperAnswers() implements ReportMessage, Prose {}

    record AClauseOf(String declaredOn) implements ReportMessage, Prose {}

    record AClauseNamed(String declaredOn, String name) implements ReportMessage, Prose {}

    record AnArmDecidedByAClauseWithNoForm(Message clause) implements ReportMessage, Prose {}

    record AnArmDecidedByAClauseReadingAFieldLeftOut(Message clause)
            implements ReportMessage, Prose {}

    record AnInvariantNotReached() implements ReportMessage, Prose {}

    record AnotherBehaviorTurningOnItsDependency() implements ReportMessage, Prose {}

    record AnotherBehaviorReachingItself() implements ReportMessage, Prose {}

    record AnotherBehaviorNotRead() implements ReportMessage, Prose {}

    record NoConditionHereSaysThat(String operation, String proposition)
            implements ReportMessage, Prose {}

    record MoreValuesThanAreReadOneByOne() implements ReportMessage, Prose {}

    record MoreReadingsInAllThanAreMade() implements ReportMessage, Prose {}

    record MorePartsThanAStepConcludes() implements ReportMessage, Prose {}

    record MoreWaysOfKeepingElements() implements ReportMessage, Prose {}

    record MoreElementsThanAreWrittenOut() implements ReportMessage, Prose {}

    record AValueThatIsOneOfSeveral() implements ReportMessage, Prose {}

    record AHelperThatStatesDifferentThings() implements ReportMessage, Prose {}

    record AConditionTheReadingDidNotMeet() implements ReportMessage, Prose {}

    record WhichElementARunReachesFirst() implements ReportMessage, Prose {}

    // --- what a search that came to nothing came back with ---

    record NothingCouldBuildARepresentative(String at) implements ReportMessage, Prose {}

    record EveryValueTriedWasRefused(String at) implements ReportMessage, Prose {}

    record EveryValueTriedWasRefusedOfSome(String at) implements ReportMessage, Prose {}

    record NothingCouldAnswerForADependency(String at) implements ReportMessage, Prose {}

    record ATableIsWhatThisNeeds(String at) implements ReportMessage, Prose {}

    record TheSearchLeftSomethingUntried(String at) implements ReportMessage, Prose {}

    record TheGroupWasNotOffered(String at) implements ReportMessage, Prose {}

    record TheWayInPlacesAtNoClass(String at) implements ReportMessage, Prose {}

    record TheBlockIsAsLongAsItMayBe(String at) implements ReportMessage, Prose {}

    record ItWouldNeedOnePositionToBeTwoThings(String at, Message noValue)
            implements ReportMessage, Prose {}

    record ItIsPastAConditionThatNeverComesOutSo(String at, Message noValue)
            implements ReportMessage, Prose {}

    record EveryRowComposedReachesAnUnreachable(String at) implements ReportMessage, Prose {}

    record NothingToBuildACandidateAgainst() implements ReportMessage, Prose {}

    record ThisBuildComposedNoValues(String at) implements ReportMessage, Prose {}

    record TheGeneratedClassesWouldNotLink() implements ReportMessage, Prose {}

    record NoRowComposedWasSeenReachingIt(String at) implements ReportMessage, Prose {}

    record ThePositionWasWithheld() implements ReportMessage, Prose {}

    record TheRowsWereNotRead() implements ReportMessage, Prose {}

    record NoCandidateWasOffered() implements ReportMessage, Prose {}

    record NoReadingOfTheLineCouldBeSearched(String at) implements ReportMessage, Prose {}

    // --- a case a line was taken apart into ---

    record ArmOfTheConstructIn(int arm, String kind, String definition)
            implements ReportMessage, Prose {}

    record DownTheArms(String arms) implements ReportMessage, Prose {}

    record StructuralWays(String ways) implements ReportMessage, Prose {}

    record MoreStructuralWaysThanCounted() implements ReportMessage, Prose {}

    record AtMostNumericallyConsistentWays(String ways) implements ReportMessage, Prose {}

    record NumericallyConsistentWaysNotCounted(Message past) implements ReportMessage, Prose {}

    record TheStatesACountIsTakenIn() implements ReportMessage, Prose {}

    record TheWaysACountIsHeldTo() implements ReportMessage, Prose {}

    record WhatMadeItsPartsWasNotRead(Message past) implements ReportMessage, Prose {}

    record WhatWasHeldOfItsDerivation() implements ReportMessage, Prose {}

    record TheStepsAReadingTakes() implements ReportMessage, Prose {}

    record ItsPartsWereMadeBy(String factors) implements ReportMessage, Prose {}

    record PartsMadeByNothingNamed(String unattributed, String parts)
            implements ReportMessage, Prose {}

    record WhatTheNumbersLeaveOfThem(String diagnoses) implements ReportMessage, Prose {}

    record ComparisonsTurnAtOnePoint(String comparisons, String quantity, String ways)
            implements ReportMessage, Prose {}

    record ComparisonsTurnAtPoints(String comparisons, String quantity, String points, String ways)
            implements ReportMessage, Prose {}

    record RemaindersComeOutOneWay(String comparisons, String dividend, String divisor)
            implements ReportMessage, Prose {}

    record RemaindersComeOutWays(String comparisons, String dividend, String divisor, String ways)
            implements ReportMessage, Prose {}

    record ChoicesMultiplyTheHelper(String helper, Message at, Message inside)
            implements ReportMessage, Prose {}

    record TheCallIsWrittenInsideHelpers(String helpers) implements ReportMessage, Prose {}

    record TheIf() implements ReportMessage, Prose {}

    record TheMatch() implements ReportMessage, Prose {}

    record TheCasesOf(String operation) implements ReportMessage, Prose {}

    record TheCasesOfAnOperation() implements ReportMessage, Prose {}

    record ChosenOnce(Message what, String in, String ways) implements ReportMessage, Prose {}

    record ChosenTimes(Message what, String in, String ways, String times)
            implements ReportMessage, Prose {}

    record TheCallOnOneApplication(String operation, String in) implements ReportMessage, Prose {}

    record TheCallOnApplications(String operation, String in, String applications)
            implements ReportMessage, Prose {}

    record KeptBy(String what) implements ReportMessage, Prose {}

    record TheWaysElementsAreKeptOnce(Message by, String ways) implements ReportMessage, Prose {}

    record TheWaysElementsAreKept(Message by, String ways, String times)
            implements ReportMessage, Prose {}

    // --- what the figures and populations of this compiler are called ---

    record ThisCompilerStoppedAtFigures(Message budgets) implements ReportMessage, Prose {}

    record ThePlanOfTheValueWasLimitedBy(Message budgets) implements ReportMessage, Prose {}

    record ThisCompilerWritesSomeOfThem(Message populations) implements ReportMessage, Prose {}

    record ThisCompilerCouldNotHoldThem(Message capacities) implements ReportMessage, Prose {}

    record WaysATotalIsSpread() implements ReportMessage, Prose {}

    record PlacesAPairIsTriedAtOnALine() implements ReportMessage, Prose {}

    record ValuesThatAnswerSeveralOfTheirNumbers() implements ReportMessage, Prose {}

    record ValuesAtARemainderOfAFormNotWhole() implements ReportMessage, Prose {}

    record PlacesInARunThatAreNamed() implements ReportMessage, Prose {}

    record ElementsChosenForACount() implements ReportMessage, Prose {}

    record KeysPlacedAtTheNumberTheirElementsComeTo() implements ReportMessage, Prose {}

    record KeysOfOneFoldAskedTogether() implements ReportMessage, Prose {}

    record EndsOfAKeyWrittenAsOneElement() implements ReportMessage, Prose {}

    record TotalsFromAPutWrittenAsOneElement() implements ReportMessage, Prose {}

    record ElementsAComputedTotalIsSolvedFor() implements ReportMessage, Prose {}

    record MixesOfCasesATotalIsSpreadOver() implements ReportMessage, Prose {}

    record ElementsWithTheOtherFieldsHeldStill() implements ReportMessage, Prose {}

    record TreesWrittenForACount() implements ReportMessage, Prose {}

    record TreesWrittenForALine() implements ReportMessage, Prose {}

    record StringsACaseConversionIsWrittenFor() implements ReportMessage, Prose {}

    record MapsWrittenWithOneEntry() implements ReportMessage, Prose {}

    record TheRowsWhoseRunWorksOutANumber(Message candidates) implements ReportMessage, Prose {}

    record ContainersOfEverySize(String most) implements ReportMessage, Prose {}

    record WholeNumbersAtOneOf(String values) implements ReportMessage, Prose {}

    record SizesAndValues(Message sizes, Message values) implements ReportMessage, Prose {}

    record TheNextPlaceAlongAPairsLine() implements ReportMessage, Prose {}

    record ThePlaceADistanceMovesOneTo() implements ReportMessage, Prose {}

    record TheNextValueOfAProgression() implements ReportMessage, Prose {}

    record TheNextValueOfAPositionOnTheWay() implements ReportMessage, Prose {}

    record OneElementsShareOfATotal() implements ReportMessage, Prose {}

    record TheLeastCountTheConditionsLeave() implements ReportMessage, Prose {}

    record ACountALineOnACountIsTriedAt() implements ReportMessage, Prose {}

    record APlaceAStatementAboutAnElementTurnsAt() implements ReportMessage, Prose {}

    record WhatAValueTheRulesNameComesTo() implements ReportMessage, Prose {}

    record WhichThisHostHadNoRoomFor(Message what) implements ReportMessage, Prose {}

    record WhichHasNoRepresentation(Message what) implements ReportMessage, Prose {}
}
