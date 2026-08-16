package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/** What an example row, the file it is written in, and the fakes it runs against are told. */
public sealed interface ExampleMessage extends Message {

    // --- the target ---

    /** The example names something this module does not declare as a behavior. */
    @Code(DiagnosticCode.E1901)
    record NoBehaviorOfThatName(String target) implements ExampleMessage, Reported {}

    /** The target is a behavior nothing can evaluate. */
    @Code(DiagnosticCode.E1902)
    record TheTargetCannotBeEvaluated(String target) implements ExampleMessage, Reported {}

    /** What an example can run, and what this one is. */
    record WhatAnExampleRuns(String here) implements ExampleMessage, Supporting {}

    /** `examples for` names a module that is not being compiled. */
    @Code(DiagnosticCode.E1907)
    record TheModuleIsNotBeingCompiled(String module) implements ExampleMessage, Reported {}

    // --- the row ---

    /** The row hands over a different number of inputs than the behavior takes. */
    @Code(DiagnosticCode.E1903)
    record TheRowHandsOverAnotherNumberOfInputs(String target, String takes, String given)
            implements ExampleMessage, Reported {}

    /** An input of the row could not be built. */
    @Code(DiagnosticCode.E1903)
    record AnInputCouldNotBeBuilt(String target, String at, String why) implements ExampleMessage, Reported {}

    /** The expected value could not be built. */
    @Code(DiagnosticCode.E1903)
    record TheExpectedValueCouldNotBeBuilt(String target, String why) implements ExampleMessage, Reported {}

    /** The row expects a case the behavior does not answer with. */
    @Code(DiagnosticCode.E1904)
    record NotOneOfTheResultCases(String expected, String target) implements ExampleMessage, Reported {}

    /** Which cases it does answer with. */
    record TheResultCasesAre(String cases) implements ExampleMessage, Supporting {}

    /** The row does not hold. */
    @Code(DiagnosticCode.E1905)
    record TheRowDoesNotHold() implements ExampleMessage, Reported {}

    /** Where the two are not of one type, which reading the two values does not say: an encoder
     *  writes a newtype as the base it wraps, so both sides read alike. */
    record TheTwoAreOfDifferentTypes(String at, String expected, String actual)
            implements ExampleMessage, Supporting {}

    /** What the row said and what came back. */
    record WhatTheRowSaid(String said) implements ExampleMessage, Supporting {}

    /**
     * A name is on more than one row of one behavior, so it says which row nowhere.
     *
     * <p>Said at every row that carries it, in the source that row is written in. Which of them is
     * the one that should have been named otherwise is not a question the language answers.
     */
    @Code(DiagnosticCode.E1925)
    record TheNameIsOnMoreThanOneRow(String name, String target) implements ExampleMessage, Reported {}

    /** The row reached a point the model says cannot arise. */
    @Code(DiagnosticCode.E1911)
    record TheRowReachedAnUnreachablePoint(String reason) implements ExampleMessage, Reported {}

    /** Which of the two that is. */
    record EitherTheRowOrTheReasonIsWrong() implements ExampleMessage, Supporting {}

    // --- the file ---

    /** An `examples for` file holds only what belongs in one. */
    @Code(DiagnosticCode.E1906)
    record AnExamplesFileHoldsOnlyExamples() implements ExampleMessage, Reported {}

    /** A value the file names is already declared by the module it is about. */
    @Code(DiagnosticCode.E1906)
    record TheNameIsAlreadyDeclared(String name, String module) implements ExampleMessage, Reported {}

    // --- the fakes ---

    /** A dependency has no fake. */
    @Code(DiagnosticCode.E1908)
    record ADependencyHasNoFake(String behavior, String dependency) implements ExampleMessage, Reported {}

    /** The same, where the dependency is reached through something else. */
    @Code(DiagnosticCode.E1908)
    record ADependencyReachedThroughHasNoFake(String behavior, String dependency, String through)
            implements ExampleMessage, Reported {}

    /** What to write for it. */
    record WriteAFakeLikeThis(String shown) implements ExampleMessage, Supporting {}

    /** The fake's value could not be built. */
    @Code(DiagnosticCode.E1908)
    record TheFakeValueCouldNotBeBuilt(String dependency, String why) implements ExampleMessage, Reported {}

    /** The fake itself could not be built. */
    @Code(DiagnosticCode.E1908)
    record TheFakeCouldNotBeBuilt(String dependency, String why) implements ExampleMessage, Reported {}

    /**
     * A row states arguments an earlier row of the table states, so the table answers with that one.
     *
     * <p>The dispatch takes the first row stating what it is asked, so a second is written and never
     * reached.
     */
    @Code(DiagnosticCode.E1926)
    record AnEarlierRowAnswersTheseArguments(String fake) implements ExampleMessage, Reported {}

    /** A `_` row is followed by another, which is what the table falls through to instead. */
    @Code(DiagnosticCode.E1926)
    record ALaterDefaultRowAnswersInstead(String fake) implements ExampleMessage, Reported {}

    /** Where the row that does answer is written. */
    record TheRowThatAnswersIsHere(String fake) implements ExampleMessage, Supporting {}

    /** A fake was asked for an input its table has no output for. */
    @Code(DiagnosticCode.E1909)
    record AFakeHadNoOutputForAnInput(String input) implements ExampleMessage, Reported {}

    /**
     * What answers the behavior was built against another revision of the module, and the two say
     * different things about something a value crossing between them depends on.
     */
    @Code(DiagnosticCode.E1927)
    record TheAnswerIsOfAnotherBuild(String target, String module, String declaration)
            implements ExampleMessage, Reported {}

    /** What to do about it: the two are one model, built twice. */
    record BuildWhatAnswersItAgainstThisRevision(String module)
            implements ExampleMessage, Supporting {}

    /**
     * Whether what answers the behavior was built against this module could not be told — which is
     * not the same as their disagreeing, and is said as its own thing for that reason.
     */
    @Code(DiagnosticCode.E1927)
    record WhetherTheAnswerIsOfThisModuleCannotBeTold(String target, String module)
            implements ExampleMessage, Reported {}

    /** Nothing was published for the module: the classes carry no declarations at all. */
    record ItsClassesCarryNoDeclarations(String module) implements ExampleMessage, Supporting {}

    /** Declarations were published and this compiler does not read them. */
    record WhatItPublishedCannotBeReadHere(String module) implements ExampleMessage, Supporting {}

    /** The answer never said which build's declarations it reads a row's values by. */
    record ItDidNotSayWhichBuildItReadsBy(String module) implements ExampleMessage, Supporting {}

    /** The side that could not be read is the one the rows are written for, not the answer's. */
    record ThisCompileCannotReadItsOwnDeclarationsOf(String module)
            implements ExampleMessage, Supporting {}

    // --- what the evaluation could not finish ---

    /** The evaluation did not answer in time. */
    @Code(DiagnosticCode.E1923)
    record TheEvaluationDidNotAnswer(String within) implements ExampleMessage, Reported {}

    /** What that says and what it does not. */
    record NotAnsweringIsNotNotTerminating() implements ExampleMessage, Supporting {}

    /** The evaluation spent its step budget. */
    @Code(DiagnosticCode.E1910)
    record TheEvaluationSpentItsSteps(String budget) implements ExampleMessage, Reported {}

    /** What that says and what it does not. */
    record SpendingTheBudgetIsNotDiverging() implements ExampleMessage, Supporting {}

    /** The evaluation reached its recursion-depth limit. */
    @Code(DiagnosticCode.E1910)
    record TheEvaluationReachedItsDepthLimit(String limit) implements ExampleMessage, Reported {}

    /** What that says and what it does not. */
    record ReachingTheDepthLimitIsNotDiverging() implements ExampleMessage, Supporting {}

    /** The JVM stack ran out before the depth limit did. */
    @Code(DiagnosticCode.E1924)
    record TheStackRanOutBeforeTheDepthLimit(String stack, String limit)
            implements ExampleMessage, Reported {}

    /** What to do about it. */
    record TheDepthLimitIsWhatShouldStopIt() implements ExampleMessage, Supporting {}

    // --- what the rows do not cover ---

    /** No row expects a case the signature declares. */
    @Code(DiagnosticCode.E1913)
    record NoRowExpectsThatCase(String caseName, String behavior) implements ExampleMessage, Reported {}

    /** What to write for it. */
    record WriteARowExpectingThatCase(String caseName) implements ExampleMessage, Supporting {}

    /** No row applies the behavior to a case one of its inputs declares. */
    @Code(DiagnosticCode.E1915)
    record NoRowAppliesItToThatCase(String caseName, String at, String behavior)
            implements ExampleMessage, Reported {}

    /** No row sits on a boundary an invariant draws. */
    @Code(DiagnosticCode.E1916)
    record NoRowIsAtThatBoundary(String at, String value, String rule) implements ExampleMessage, Reported {}

    /**
     * The same, where a guard drew the line.
     *
     * <p>A rule of its own because a guard has no name to put in the other one's slot. What went
     * there was a phrase built in Java — `a guard` — which is a rendering, so it read as English in
     * every language the rest of the sentence was written in. A type and an invariant have names,
     * and a name is the same in every language; this has none, so the words are the catalog's.
     *
     * <p>Where the guard is written is not here either. It is a place, and a place is pointed at.
     */
    @Code(DiagnosticCode.E1916)
    record NoRowIsAtTheLineAGuardDrew(String at, String value)
            implements ExampleMessage, Reported {}

    /** Said beside the guard a line was drawn by, the sentence naming the rule without a place —
     *  a guard has no name, and where it is written is a place a renderer resolves a file for. */
    record TheGuardThatDrawsTheLine() implements ExampleMessage, Supporting {}

    /** What a row on the line tells apart. */
    record ARowOnTheLineTellsTwoRulesApart() implements ExampleMessage, Supporting {}

    /** No row goes through an arm of the body. */
    @Code(DiagnosticCode.E1918)
    record NoRowGoesThroughThatArm(String arm, String behavior) implements ExampleMessage, Reported {}

    /** Which of the two that is. */
    record EitherARowIsMissingOrNothingReachesIt() implements ExampleMessage, Supporting {}

    // --- a stand-in and a row that disagree ---

    /** A row and a fake state different answers for one input. */
    @Code(DiagnosticCode.E1919)
    record TheRowAndTheFakeDisagree(String behavior) implements ExampleMessage, Reported {}

    /** The same, where the stand-in is a `with`. */
    @Code(DiagnosticCode.E1919)
    record TheRowAndTheWithDisagree(String behavior) implements ExampleMessage, Reported {}

    /** What each of them says. */
    record WhatTheRowSaysAndWhatTheFakeSays(String row, String fake) implements ExampleMessage, Supporting {}

    /** The same, for a `with`. */
    record WhatTheRowSaysAndWhatTheWithSays(String row, String with) implements ExampleMessage, Supporting {}

    /** Where the fake that disagrees is written — the other half of the disagreement, since neither
     *  statement is the one the model is to be held to. */
    record TheFakeRowIsHere(String behavior) implements ExampleMessage, FindingRegion {}

    /** Where the `with` that disagrees is written, for the same reason. */
    record TheWithIsHere(String behavior) implements ExampleMessage, FindingRegion {}

    // --- a table that could not be built, so nothing it states was checked ---

    /** Building the fake's table spent its step budget. */
    @Code(DiagnosticCode.E1921)
    record TheTableSpentItsSteps(String fake, String budget) implements ExampleMessage, Reported {}

    /** Building the fake's table reached the depth limit. */
    @Code(DiagnosticCode.E1921)
    record TheTableReachedItsDepthLimit(String fake, String limit) implements ExampleMessage, Reported {}

    /** Building the fake's table ran out of JVM stack. */
    @Code(DiagnosticCode.E1921)
    record TheTableRanOutOfStack(String fake, String limit) implements ExampleMessage, Reported {}

    /** Building the fake's table did not answer in time. */
    @Code(DiagnosticCode.E1921)
    record TheTableDidNotAnswer(String fake, String within) implements ExampleMessage, Reported {}

    /** What a table over its steps says. */
    record TheTableGoesRoundTooManyTimes(String fake) implements ExampleMessage, Supporting {}

    /** What a table past the depth limit says. */
    record TheTableRecursesTooDeeply(String fake) implements ExampleMessage, Supporting {}

    /** What a table that overran the stack says. */
    record TheStackGotThereFirst(String fake) implements ExampleMessage, Supporting {}

    /** What a table that did not answer says. */
    record TheTableNotAnsweringIsNotTheTableBeingWrong(String fake) implements ExampleMessage, Supporting {}

    /** The fake could not be compared with the rows: its table spent its steps. */
    @Code(DiagnosticCode.E1920)
    record NotComparedTheTableSpentItsSteps(String behavior, String budget)
            implements ExampleMessage, Reported {}

    /** The same, at the depth limit. */
    @Code(DiagnosticCode.E1920)
    record NotComparedTheTableReachedItsDepthLimit(String behavior, String limit)
            implements ExampleMessage, Reported {}

    /** The same, out of stack. */
    @Code(DiagnosticCode.E1920)
    record NotComparedTheTableRanOutOfStack(String behavior, String limit)
            implements ExampleMessage, Reported {}

    /** The same, unanswered. */
    @Code(DiagnosticCode.E1920)
    record NotComparedTheTableDidNotAnswer(String behavior, String within)
            implements ExampleMessage, Reported {}

    /** What each of those says, in turn. */
    record TheTableComparedGoesRoundTooManyTimes(String behavior) implements ExampleMessage, Supporting {}

    record TheTableComparedRecursesTooDeeply(String behavior) implements ExampleMessage, Supporting {}

    record TheStackGotThereFirstWhenComparing(String behavior) implements ExampleMessage, Supporting {}

    record NotAnsweringIsNotTwoAnswers(String behavior) implements ExampleMessage, Supporting {}
}
