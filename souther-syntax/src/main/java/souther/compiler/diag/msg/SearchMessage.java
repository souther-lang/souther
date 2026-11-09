package souther.compiler.diag.msg;

/**
 * What the examples report says about a search for a row: why no row was composed at a class, a
 * point or an arm, what stopped the search, and what a strategy does not do.
 *
 * <p>Each sentence and each clause is a message of its own, and a sentence that says another one
 * inside it carries it as a value, so a translation never assembles a sentence out of English word
 * order. Where the wording turns on a value — one or several, a value that is settled or not — the
 * two wordings are two messages. Code the author wrote, a path and a number are carried as text.
 */
public sealed interface SearchMessage extends Message {

    // --- why a finding is not applicable (GenerationOutcome.NotApplicable.Reason) ---

    record NothingWasMeasured() implements SearchMessage, Prose {}

    record TheMeasureDoesNotEstablishThis() implements SearchMessage, Prose {}

    record AFactAboutTheModel() implements SearchMessage, Prose {}

    record AnAccountOfWhatTheRowsDid() implements SearchMessage, Prose {}

    record ARowHereIsWaitingForItsAnswer() implements SearchMessage, Prose {}

    record EveryRowHereReachesAnUnreachable() implements SearchMessage, Prose {}

    // --- why no strategy takes a finding (GenerationOutcome.NotSupported.Reason) ---

    record NoWayIntoThisArmCanBeNamed() implements SearchMessage, Prose {}

    record TheWaysIntoThisArmAreNotEnumerable() implements SearchMessage, Prose {}

    record TheWaysIntoThisArmAreNotToldApart() implements SearchMessage, Prose {}

    record MoreWaysInThanTheReadingHolds() implements SearchMessage, Prose {}

    record TheArmRunsWhereSomethingCallsIt() implements SearchMessage, Prose {}

    record AConstructionDecidesThisArm() implements SearchMessage, Prose {}

    record NoStrategyForAnOutputCase() implements SearchMessage, Prose {}

    record NoStrategyForAWeight() implements SearchMessage, Prose {}

    record NoAxisAtThisPosition() implements SearchMessage, Prose {}

    // --- what a report calls a line and its points ---

    /** Which side of the line a point is on, said after its role. */
    record BelowTheLine() implements SearchMessage, Prose {}

    record AboveTheLine() implements SearchMessage, Prose {}

    /** Nothing, where there is nothing to add: a side no other point needs told apart from. */
    record NothingSaid() implements SearchMessage, Prose {}

    /** A rule by the name the author cited it by. */
    record TheRuleCited(String rule) implements SearchMessage, Prose {}

    record TheComparison() implements SearchMessage, Prose {}

    record TheFork() implements SearchMessage, Prose {}

    record ThePredicate() implements SearchMessage, Prose {}

    /** A rule a body wrote, after the handle that sends a reader to it. */
    record TheRuleInTheBehavior(String rule, String behavior) implements SearchMessage, Prose {}

    /** A rule whose end the declarations in {@code within} took in. */
    record RuleWithin(SearchMessage rule, SearchMessage within) implements SearchMessage, Prose {}

    /** A piece of code as the author wrote it, standing alone. */
    record Code(String code) implements SearchMessage, Prose {}

    /** One piece of code or what {@code rest} says, any of which is the answer. */
    record OrElse(String one, SearchMessage rest) implements SearchMessage, Prose {}

    // --- containers whose counts add up through containers inside them ---

    record NoGroupingOfTheLeavesMetTheCounts(String run) implements SearchMessage, Prose {}

    record NoGroupingOfTheElementsMetTheCounts(String run) implements SearchMessage, Prose {}

    record AskedForAValueWhereAnElementHoldsTheContainers(String asked)
            implements SearchMessage, Prose {}

    record NothingReadsTheWayFrom(String from, String to) implements SearchMessage, Prose {}

    // --- a container composed for counts of its elements ---

    record NothingSaysHowManyElementsMeet(String container, String each)
            implements SearchMessage, Prose {}

    record NothingSaysHowManyElementsMeetEachOf(String container, String counted)
            implements SearchMessage, Prose {}

    record TheValuesAreCountedAtTwoPlaces(String container, String apartAt, String at)
            implements SearchMessage, Prose {}

    record NothingSaysHowManyElementsItHolds(String container) implements SearchMessage, Prose {}

    record CountedInOneAndAcrossAll(String container) implements SearchMessage, Prose {}

    record CountedAcrossTheContainersHoldingThem(String container)
            implements SearchMessage, Prose {}

    record CountedAcrossAndHowManyOneHoldsIsAskedOfOne(String container)
            implements SearchMessage, Prose {}

    record NoListOrSetWrittenWhereItStands(String container) implements SearchMessage, Prose {}

    record AskedOfOneOfTheContainers(String container) implements SearchMessage, Prose {}

    record WhatAnElementAnswersReadsAContainerHoldingIt(String container)
            implements SearchMessage, Prose {}

    record ReadOffAContainerHoldingAnElement(String term, String container)
            implements SearchMessage, Prose {}

    record NoListOrSetInsideTheElements(String container) implements SearchMessage, Prose {}

    record NoListOrSet(String container) implements SearchMessage, Prose {}

    record NoCountWalkedIsOneAContainerMeets() implements SearchMessage, Prose {}

    record NoSizeHasRoomForTheCount() implements SearchMessage, Prose {}

    record NothingSaysWhereItStandsInsideAnElement(String term, String container)
            implements SearchMessage, Prose {}

    record ATotalOfAPlaceWhoseNumbersAreNotWhole(String container)
            implements SearchMessage, Prose {}

    record APartNeitherOneOfSoManyNorNumbers(String container) implements SearchMessage, Prose {}

    record TheDifferentValuesAreCounted(String apartAt, String container)
            implements SearchMessage, Prose {}

    record AnElementAStatementCouldNotBeReadAt(String unread) implements SearchMessage, Prose {}

    record NoElementIsLeftAValue(String container) implements SearchMessage, Prose {}

    record NoContainerMeetsEveryCount(String container) implements SearchMessage, Prose {}

    record TurnsOnWhichIsHandedLast(String container, String under)
            implements SearchMessage, Prose {}

    record TurnsOnTheElementsBesideIt(String container) implements SearchMessage, Prose {}

    record TurnsOnElementsNotHoldingItsValue(String container, String under)
            implements SearchMessage, Prose {}

    record NothingSaysHowOftenAnElementOccurs(String container) implements SearchMessage, Prose {}

    record NoListOrSetToHoldAnElementAsOften(String container, String type)
            implements SearchMessage, Prose {}

    record AnElementIsOnNoOrder(String container) implements SearchMessage, Prose {}

    record NoValueForAnElement(String container) implements SearchMessage, Prose {}

    record WhereItTurnsOverCouldNotBeWorkedOut(String key, String container)
            implements SearchMessage, Prose {}

    record NoContainerHoldsAnElementAsOften(String container) implements SearchMessage, Prose {}

    record AnElementIsAlikeAnother(String container, String place)
            implements SearchMessage, Prose {}

    record NoContainerHoldsAValueAtAsOften(String container, String place)
            implements SearchMessage, Prose {}

    record NothingSaysHowOftenAValueOccurs(String place) implements SearchMessage, Prose {}

    record AValueIsNotAnElementOfItsContainer(String place) implements SearchMessage, Prose {}

    record AValueIsOnNoOrder(String place) implements SearchMessage, Prose {}

    /** The rules leave nothing at a place, said where nothing else is known of it. */
    record NoValueAt(String place) implements SearchMessage, Prose {}

    record NoValueToRepeat(String place) implements SearchMessage, Prose {}

    record NoValueToRepeatThatKeeps(String place, String key) implements SearchMessage, Prose {}

    record NoContainersHoldAValueAsOften(String place) implements SearchMessage, Prose {}

    record NothingSaysHowOftenTheValueOccursAt(String key, String place)
            implements SearchMessage, Prose {}

    record StandsAtNoOneValue(String key) implements SearchMessage, Prose {}

    record NoContainersHoldTheKeysAsOften(String place) implements SearchMessage, Prose {}

    // --- containers whose elements add up to a total ---

    record EachElementIsAskedToHoldItAtTwo(String at, String one, String other)
            implements SearchMessage, Prose {}

    record TheListsOfAListAreSpreadOverOneTotalAtATime() implements SearchMessage, Prose {}

    record AMapWhoseValuesComeToATotalHasOneEntry() implements SearchMessage, Prose {}

    record NoValueHeldTheOtherFieldsStill() implements SearchMessage, Prose {}

    record AskedForAValueWhereEachElementHoldsItsShare(String asked)
            implements SearchMessage, Prose {}

    record WhichCaseTheOtherTotalsAreUnderIsNotChosen() implements SearchMessage, Prose {}

    record TheTotalsAreNotOfOneContainer() implements SearchMessage, Prose {}

    record ATotalBesideAnotherIsComputedOfAField() implements SearchMessage, Prose {}

    record ReadByMoreThanOneOfTheTotals(String field) implements SearchMessage, Prose {}

    record TheElementsAreKeptApartAt(String field) implements SearchMessage, Prose {}

    /** One way down, already written as code, that composed nothing. */
    record AWayDownComposedNothing(String ways, String demand) implements SearchMessage, Prose {}

    /** Several ways down, already written as a list of code, none of which composed anything. */
    record WaysDownComposedNothing(String ways, String demand) implements SearchMessage, Prose {}

    record NothingHereReaches(String demand) implements SearchMessage, Prose {}

    record NothingStandingAtGivesAWayDown(String at, String demand)
            implements SearchMessage, Prose {}

    // --- a value composed for one number of a row ---

    record WhatIsGatheredForItIsNotKnown(String asked) implements SearchMessage, Prose {}

    record TwoNumbersAreAskedOfOneKey() implements SearchMessage, Prose {}

    record HowManyElementsHaveItIsNotKnown(String asked) implements SearchMessage, Prose {}

    record TwoCountsAreAskedOfOneKey() implements SearchMessage, Prose {}

    record OnlyABareListIsPutTogetherOfSeveralKeys() implements SearchMessage, Prose {}

    record NothingWritesATreeForHowManyValues(String container) implements SearchMessage, Prose {}

    record ALineBesideOtherNumbersIsNotWritten() implements SearchMessage, Prose {}

    record ATreeOfSoManyNodesIsDeeper(String many) implements SearchMessage, Prose {}

    record TheNodeTheSearchStopsAtIsNotKnown(String key) implements SearchMessage, Prose {}

    record TheNodeIsNotARecordHoldingTheValue() implements SearchMessage, Prose {}

    record TheNodesBelowANodeAreNotAList() implements SearchMessage, Prose {}

    record TheValueSearchedForIsNotWrittenAtTheNode() implements SearchMessage, Prose {}

    record NoOtherValueToWriteInATreeWithoutIt() implements SearchMessage, Prose {}

    record NoOtherValueToWriteAboveTheNode() implements SearchMessage, Prose {}

    record ANodeOfTheLineIsNotWrittenInsideItsRules() implements SearchMessage, Prose {}

    record AskedToHoldTwoValues(String position) implements SearchMessage, Prose {}

    record TheKeyIsAskedToHaveMoreThanOneElement() implements SearchMessage, Prose {}

    record AskedToHoldAnotherValueThanTheKey(String at) implements SearchMessage, Prose {}

    /** A type a value wears that this module has no name for. */
    record TheModuleDoesNotExposeIt(String module, String name) implements SearchMessage, Prose {}

    record TheNameIsDeclaredHere(String name) implements SearchMessage, Prose {}

    // --- a value built, read back to be written into a row or handed on ---

    record NotAPositionTheValueBuiltHas(String path) implements SearchMessage, Prose {}

    record NothingStandsThereInTheValueBuilt(String path) implements SearchMessage, Prose {}

    record AtEachOfSeveralElements(String path, String count) implements SearchMessage, Prose {}

    record NotAContainerTheValueBuiltHas(String container) implements SearchMessage, Prose {}

    /** A value built that cannot be written, with why as a clause of its own. */
    record TheValueBuiltCannotBeWritten(String path, SearchMessage why)
            implements SearchMessage, Prose {}

    record NothingWasComposedThere() implements SearchMessage, Prose {}

    record NoneOfThemIsWhatWasComposed() implements SearchMessage, Prose {}

    record NothingWritesAValueOfThisType() implements SearchMessage, Prose {}

    record NotAValueOfThePrimitive(String prim) implements SearchMessage, Prose {}

    record ADecimalThisFarHasNoLiteral() implements SearchMessage, Prose {}

    record TheValueBuiltHoldsNothingAt(String field) implements SearchMessage, Prose {}

    /** A value the observation could not read, with the reason the run gave. */
    record TheValueCouldNotBeReadBack(String reason) implements SearchMessage, Prose {}

    record ALimitStoppedTheObservation() implements SearchMessage, Prose {}

    record NotTheConstructionThePositionDeclares() implements SearchMessage, Prose {}

    record NothingBuiltTheValueToSayWhichElements(String container)
            implements SearchMessage, Prose {}

    record NothingBuiltTheValueToSayWhatStandsThere(String at) implements SearchMessage, Prose {}

    record NothingComposedBeforeHandedItOn(String at) implements SearchMessage, Prose {}

    record NothingComposedBeforeHandsOnTheElements(String container)
            implements SearchMessage, Prose {}

    record IsToHold(String at, String value) implements SearchMessage, Prose {}

    record IsToHoldAValueOtherThan(String at, String value) implements SearchMessage, Prose {}

    record AreToHoldOneValue(String one, String other) implements SearchMessage, Prose {}

    record AreToHoldTwoValues(String one, String other) implements SearchMessage, Prose {}

    record NotHandedTheValueForEachElement(String container, String value, String around)
            implements SearchMessage, Prose {}

    // --- two things a row is asked to hold at one location ---

    record WouldHaveToHoldTwoValuesAtOnce(String at) implements SearchMessage, Prose {}

    record InsideAndEachAskedForAValue(String inner, String outer)
            implements SearchMessage, Prose {}

    record AskedToHoldTwoNumbersOfElements(String at) implements SearchMessage, Prose {}

    record AskedForAValueAndHowMany(String at) implements SearchMessage, Prose {}

    record TheValueAlreadySaysHowMany(String counted, String valued)
            implements SearchMessage, Prose {}

    // --- a class with no value to stand in it ---

    record NothingComposedAValueOfTheType(String type) implements SearchMessage, Prose {}

    record NothingComposedAValueOfTheCase(String name) implements SearchMessage, Prose {}

    record TheModelsDecimalsPutThisValuePastARow() implements SearchMessage, Prose {}

    record NothingCanWriteAValueOfThisPosition() implements SearchMessage, Prose {}

    record NothingComposedAStringInThisClass() implements SearchMessage, Prose {}

    /** Nothing writes what {@code what} describes, which is a value of a class. */
    record NothingHereWrites(SearchMessage what) implements SearchMessage, Prose {}

    record NothingHereComposedIt(SearchMessage what) implements SearchMessage, Prose {}

    record AValueWhoseMeasureIsInThisRange(SearchMessage measure) implements SearchMessage, Prose {}

    record AValueWhoseMeasureIsTheOneSingledOut(SearchMessage measure)
            implements SearchMessage, Prose {}

    record AValueWhoseMeasureIsNoneSingledOut(SearchMessage measure) implements SearchMessage, Prose {}

    /** What a range is a range of, where it is what an operation the author wrote answers. */
    record TheOperation(String operation) implements SearchMessage, Prose {}

    record TheValueItself() implements SearchMessage, Prose {}

    record NumberOfCodePointsThatAre(String counted) implements SearchMessage, Prose {}

    /** Code points counted in the string as a transformation writes it, the code before and after
     *  the string carried apart so that the catalog names the string. */
    record NumberOfCodePointsThatAreIn(String counted, String before, String after)
            implements SearchMessage, Prose {}

    record SumOfTheCodePoints() implements SearchMessage, Prose {}

    record CodePointAt(String index) implements SearchMessage, Prose {}

    // --- a row composed for a combination or a point, and what kept it from being one ---

    /**
     * What the model said in refusing a value, in the words the run of its construction gave.
     *
     * <p>The text is the evaluation's and not this compiler's, so it is carried as it came.
     */
    record RefusedInItsOwnWords(String why) implements SearchMessage, Prose {}

    record ItDoesNotStandWhereItWasPut(String term, String at) implements SearchMessage, Prose {}

    record NoRowWasRunToAnAnswer() implements SearchMessage, Prose {}

    record NoRowWasRunToAnAnswerAndARunRanOut() implements SearchMessage, Prose {}

    record NoCaseHoldsThemAll() implements SearchMessage, Prose {}

    record ACaseWasNotRead() implements SearchMessage, Prose {}

    record EachIsToHoldAValueOfAnother(String parameters) implements SearchMessage, Prose {}

    record NothingTheseClassesCanStandBesideWasLeft() implements SearchMessage, Prose {}

    record ItsClassLeavesItNoRoom(String key) implements SearchMessage, Prose {}

    record ThePositionsAreNotInOneValue() implements SearchMessage, Prose {}

    record APositionHasNothingLeftAtIt() implements SearchMessage, Prose {}

    record WouldHaveToStandAtTwoPlacesAtOnce(String at) implements SearchMessage, Prose {}

    record WrittenUnderACaseTheWayDoesNotTake(String at) implements SearchMessage, Prose {}

    record WouldHaveToBeBoth(String at, String one, String other)
            implements SearchMessage, Prose {}

    record TheWayTakesACaseItsClassesDoNot() implements SearchMessage, Prose {}

    record AskedByTheWayToHoldBoth(String at) implements SearchMessage, Prose {}

    record AskedByTheWayAndWrittenAnother(String at, String value)
            implements SearchMessage, Prose {}

    record TheRulesLeaveNoRoomForTheValue(String at, String needed, String most)
            implements SearchMessage, Prose {}

    record HoldsNothingThatCouldBeBuiltUnderIt(String at) implements SearchMessage, Prose {}

    /** A position that stands at one of {@code cases}, with no word for which. */
    record NothingSaidWhichOfThemItIs(String at, SearchMessage cases) implements SearchMessage, Prose {}

    record StandsAtNoCaseTheRowCanBe(String at) implements SearchMessage, Prose {}

    record HandedAValueInsideAValueComposedWhole(String at) implements SearchMessage, Prose {}

    record WrittenAsAWholeValueThisDoesNotBuild(String container)
            implements SearchMessage, Prose {}

    record ElementsWrittenAlikeAreAskedTwoValues(String at) implements SearchMessage, Prose {}

    // --- what a figure of the composing counts (CompositionBudget) ---

    record ElementsAProposalHolds() implements SearchMessage, Prose {}

    record CharactersAProposalHolds() implements SearchMessage, Prose {}

    record PairingsBuiltAtOnce() implements SearchMessage, Prose {}

    record ElementsATotalIsSpreadOver() implements SearchMessage, Prose {}

    record ShapesOfATotalOffered() implements SearchMessage, Prose {}

    record ElementsACountIsComposedWith() implements SearchMessage, Prose {}

    record ContainersACountIsOffered() implements SearchMessage, Prose {}

    record SharesACountIsTriedAt() implements SearchMessage, Prose {}

    record TuplesOfCountsARelationIsTriedAt() implements SearchMessage, Prose {}

    record TotalsACountIsTriedAt() implements SearchMessage, Prose {}

    record RunsACountsElementsCanComeTo() implements SearchMessage, Prose {}

    record ValuesAnElementIsMovedToTried() implements SearchMessage, Prose {}

    record CountsOfKeysTried() implements SearchMessage, Prose {}

    record ValuesAnElementIsChosenAmong() implements SearchMessage, Prose {}

    record ElementsAnInnerContainerIsListedWith() implements SearchMessage, Prose {}

    record WaysDownToATotalTried() implements SearchMessage, Prose {}

    record WaysUnderTheCasesTried() implements SearchMessage, Prose {}

    record CasesARuleAboveIsPlannedUnder() implements SearchMessage, Prose {}

    record WaysAWayIsLookedAlong() implements SearchMessage, Prose {}

    record ChoicesOnAWayLookedAt() implements SearchMessage, Prose {}

    record WalksAWayIsReadAgainWith() implements SearchMessage, Prose {}

    record PairsOfBoundsAWayIsReadAgainWith() implements SearchMessage, Prose {}

    record ChoicesOfInputNumbersLookedAt() implements SearchMessage, Prose {}

    record PairsOfInputNumbersAndAnAnswerTried() implements SearchMessage, Prose {}

    record PlacesAPairIsTriedAt() implements SearchMessage, Prose {}

    record PlacesAPairIsLookedAt() implements SearchMessage, Prose {}

    record StepsASearchMayTake() implements SearchMessage, Prose {}

    record AssignmentsASearchComposes() implements SearchMessage, Prose {}

    record ValuesOfAnUnboundedProgressionTried() implements SearchMessage, Prose {}

    record LevelsASideIsAskedAt() implements SearchMessage, Prose {}

    record DivisorsOfAProductTried() implements SearchMessage, Prose {}

    record DivisorsOfARemainderTried() implements SearchMessage, Prose {}

    record RemaindersASumIsTriedAt() implements SearchMessage, Prose {}

    record TimesTheRulesAreAskedAgain() implements SearchMessage, Prose {}

    record ValuesAPositionOnTheWayIsTriedAt() implements SearchMessage, Prose {}

    record PlacesAPositionOnTheWayIsLookedAt() implements SearchMessage, Prose {}

    record AssignmentsOnTheWayComposedFor() implements SearchMessage, Prose {}

    record ValuesThePositionsOnTheWayAreTriedAt() implements SearchMessage, Prose {}

    record ValuesAPointIsTriedWith() implements SearchMessage, Prose {}

    record RowsBesideARunAreMadeForAPoint() implements SearchMessage, Prose {}

    record DepthAConstructionPlanDescends() implements SearchMessage, Prose {}

    record PathsOfADecisionRead() implements SearchMessage, Prose {}

    record ConditionsADecisionTakesInToProve() implements SearchMessage, Prose {}

    record ReadingsOfOneCondition() implements SearchMessage, Prose {}

    record TotalReadingsOfOneCondition() implements SearchMessage, Prose {}

    record PartsADerivationConcludes() implements SearchMessage, Prose {}

    record WaysAStatementIsWrittenOutOver() implements SearchMessage, Prose {}

    record PartsTheChoicesOfACountComeTo() implements SearchMessage, Prose {}

    record AlternativesAPathTries() implements SearchMessage, Prose {}

    record StepsAStatementIsReadIn() implements SearchMessage, Prose {}

    record CasesALineIsTakenApartInto() implements SearchMessage, Prose {}

    record CasesALineIsAskedIn() implements SearchMessage, Prose {}

    record NumbersOfASetTried() implements SearchMessage, Prose {}

    record CombinationsOfTotalsTried() implements SearchMessage, Prose {}

    record CodePointsAStringIsSearchedInFull() implements SearchMessage, Prose {}

    record CodePointsBeyondACountAStringIsLookedFor() implements SearchMessage, Prose {}

    record RunsRepairingARow() implements SearchMessage, Prose {}

    record RowsAWalkHandsTheChoiceOfARow() implements SearchMessage, Prose {}

    record PiecesAStringIsPutTogetherOf() implements SearchMessage, Prose {}

    record StringsOfTheRowAPieceIsTakenFrom() implements SearchMessage, Prose {}

    record ElementsASideIsSearchedOver() implements SearchMessage, Prose {}

    record NumbersASideIsBalancedFrom() implements SearchMessage, Prose {}

    // --- what a figure of the rest of the work counts (WorkFigure) ---

    record ReadingsOfARowAtAPoint() implements SearchMessage, Prose {}

    record ElementsAWalkWritesOut() implements SearchMessage, Prose {}

    record FieldsARuleIsFollowedDown() implements SearchMessage, Prose {}

    record PartsAPathSettles() implements SearchMessage, Prose {}

    record PairsOfClassesCounted() implements SearchMessage, Prose {}

    record CombinationsOfAGroupMeasured() implements SearchMessage, Prose {}

    record RunsReplacingAnArm() implements SearchMessage, Prose {}

    record NodesAForkCarries() implements SearchMessage, Prose {}

    record ReadingsOfACombinationTried() implements SearchMessage, Prose {}

    record RunsForOneReading() implements SearchMessage, Prose {}

    record CandidatesARepairBuilds() implements SearchMessage, Prose {}

    record AssignmentsARepairLooksAt() implements SearchMessage, Prose {}

    record AdmittedValuesOneMachine() implements SearchMessage, Prose {}

    record AdmittedValuesInAll() implements SearchMessage, Prose {}

    record OrderedExtentOneMachine() implements SearchMessage, Prose {}

    record OrderedExtentInAll() implements SearchMessage, Prose {}

    record BehaviorDistinctionsOneMachine() implements SearchMessage, Prose {}

    record BehaviorDistinctionsInAll() implements SearchMessage, Prose {}

    record RuleSetsOneMachine() implements SearchMessage, Prose {}

    record RuleSetsInAll() implements SearchMessage, Prose {}

    record StringsPartedOneMachine() implements SearchMessage, Prose {}

    record StringsPartedInAll() implements SearchMessage, Prose {}

    record EvaluationSteps() implements SearchMessage, Prose {}

    record RecursionDepth() implements SearchMessage, Prose {}

    record CompilerTime() implements SearchMessage, Prose {}

    record ObservedDepth() implements SearchMessage, Prose {}

    record ObservedNodes() implements SearchMessage, Prose {}

    record ObservedElements() implements SearchMessage, Prose {}

    record ObservedText() implements SearchMessage, Prose {}
}
