package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/**
 * What a source that did not read is told.
 *
 * <p>Which part of the language was being read is the rule a syntax error reports, and a reader
 * looking one up is not asking about the others. Where the parser meets the same missing token
 * reading a declaration and reading a pattern, that is two messages of one wording rather than one
 * message the site picks a code for.
 */
public sealed interface ParseMessage extends Message {

    /**
     * A declaration was being read and the token that came next was not the one it needs.
     *
     * <p>The two it carries are what {@link souther.compiler.diag.Messages#text} renders: a literal
     * symbol is the same in every language and is carried as written, and a category of token — a
     * name, a literal, the end of input — is carried as the phrase to look up, because the site that
     * raised this has no language to write it in.
     */
    @Code(DiagnosticCode.E2301)
    record ADeclarationExpectedSomethingElse(Object expected, Object found) implements ParseMessage, Reported {}

    /** The same, while reading an expression. */
    @Code(DiagnosticCode.E2302)
    record AnExpressionExpectedSomethingElse(Object expected, Object found) implements ParseMessage, Reported {}

    /** The same, while reading a pattern. */
    @Code(DiagnosticCode.E2303)
    record APatternExpectedSomethingElse(Object expected, Object found) implements ParseMessage, Reported {}

    /** The same, while reading an example. */
    @Code(DiagnosticCode.E2304)
    record AnExampleExpectedSomethingElse(Object expected, Object found) implements ParseMessage, Reported {}

    /** Nothing here can begin an expression. */
    @Code(DiagnosticCode.E2302)
    record AnExpressionWasExpected() implements ParseMessage, Reported {}

    /** Nothing here can be a literal. */
    @Code(DiagnosticCode.E2305)
    record ALiteralWasExpected() implements ParseMessage, Reported {}

    /** Nothing here can be a line of a block. */
    @Code(DiagnosticCode.E2302)
    record AStatementWasExpected() implements ParseMessage, Reported {}

    /** Nothing here can be a pattern. */
    @Code(DiagnosticCode.E2303)
    record APatternWasExpected() implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E2301)
    record ASourceFileStartsWithAModuleDeclaration() implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E2301)
    record ATopLevelDefinitionStartsWithAKeyword() implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E2301)
    record ABehaviorIsWrittenWithAColonOrAnEquals() implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E1402)
    record IntrinsicIsACorePrivilege() implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E1402)
    record PrivateIsACorePrivilege() implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E1402)
    record ATypeVariableIsOnlyAllowedInTheCore(String variable) implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E1402)
    record AnOptionalIsOnlyWrittenOnAFieldOrInTheCore() implements ParseMessage, Reported {}

    /** What to write instead. */
    record LeaveTheTypeOffAndTheOptionalIsInferred() implements ParseMessage, Supporting {}

    @Code(DiagnosticCode.E1308)
    record AQuestionMarkFollowsASumOfCases(String cases) implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E1310)
    record UnreachableStatesItsReasonAsAString() implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E2302)
    record ABlockEndsInOneExpression() implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E2303)
    record OptionsWrappedValueIsBoundPositionally() implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E2303)
    record ACaseValueIsBoundWithAs(String caseName, String bound) implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E2303)
    record ARecordsFieldsAreDestructuredDirectly() implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E1007)
    record ANewtypeCannotWrapATuple() implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E1007)
    record ANewtypeCannotWrapAFunction() implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E1020)
    record ASumsCasesAreDeclaredNamedData() implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E2304)
    record AnExampleOnlyFileStartsWithItsModule() implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E2301)
    record ADependencyClauseIsTwoWords() implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E2301)
    record ALetWithNoParametersIsWrittenWithoutParens(String name) implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E2304)
    record AnExampleNeedsAtLeastOneRow() implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E2304)
    record AFakeNeedsAtLeastOneRow() implements ParseMessage, Reported {}

    /**
     * A row was written with a name that names nothing.
     *
     * <p>Read here rather than where the row is checked, because it is a question about the literal:
     * a row that wrote no name is a row without one, and a row that wrote an empty one meant to say
     * which row it is and did not. The two are different mistakes and only one of them is a mistake.
     */
    @Code(DiagnosticCode.E2304)
    record ARowNameSaysNothing() implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E2306)
    record ATypeVariableNeedsANameAfterTheApostrophe() implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E2305)
    record AFractionalLiteralNeedsTheMSuffix(String literal) implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E2305)
    record AStringLiteralIsNotClosed() implements ParseMessage, Reported {}

    /**
     * A backslash written before something the language does not read as an escape.
     *
     * <p>Refused rather than read as the character alone: dropping the backslash would take a
     * character the author wrote out of the value and say nothing, so a mistyped `\d` would become
     * `d` and a pattern would be run against text nobody wrote.
     */
    @Code(DiagnosticCode.E2305)
    record AnEscapeIsNotOneTheLanguageReads(String escaped) implements ParseMessage, Reported {}

    @Code(DiagnosticCode.E2306)
    record AnUnexpectedCharacter(String character) implements ParseMessage, Reported {}

    /**
     * A name written beginning with {@code _}.
     *
     * <p>An underscore carries a name on and begins none, so {@code foo_bar} is a name and
     * {@code _foo} is not. Refused rather than read as the discard followed by a name, which would
     * make one written word into two the author did not write.
     */
    @Code(DiagnosticCode.E2306)
    record ANameDoesNotBeginWithAnUnderscore(String written) implements ParseMessage, Reported {}

    /**
     * A {@code $} in the source.
     *
     * <p>It is not a character a name is written with, and it is the mark the compiler spells its
     * own names by — the classes and locals it generates beside the ones the author declares. The
     * two sets of names have to be disjoint, so the character that separates them is refused where
     * a name is written rather than left to collide.
     */
    @Code(DiagnosticCode.E2306)
    record ADollarIsNotWrittenInAName() implements ParseMessage, Reported {}

    /**
     * A source with no {@code module} header, named after something that is not a name.
     *
     * <p>A name written in a source file was read as one by the scan. The name a header-less source
     * is given was read by nothing — it is a file's stem, or what an embedding passed in — and it
     * becomes the module's name all the same, so it is held to the same rule here. Without this a
     * module could be called what no module may declare itself.
     */
    @Code(DiagnosticCode.E2301)
    record ASourceIsNamedAfterSomethingThatIsNotAName(String given)
            implements ParseMessage, Reported {}

    /** `Some(v)` opens a wrapped newtype, and binding the whole value is written without parens. */
    @Code(DiagnosticCode.E2303)
    record SomeParensOpenAWrappedNewtype(String newtype) implements ParseMessage, Reported {}

    /** A `|` on a data field, which takes the one type the field has. */
    @Code(DiagnosticCode.E2307)
    record AFieldTypeIsNotAnAnonymousUnion(String field) implements ParseMessage, Reported {}

    /** A `|` inside another type — a type argument, a tuple's member. */
    @Code(DiagnosticCode.E2307)
    record AnAnonymousUnionIsNotWrittenInsideAnotherType() implements ParseMessage, Reported {}

    /** A `?` inside another type — a type argument, a tuple's member. */
    @Code(DiagnosticCode.E2308)
    record AnOptionalIsNotWrittenInsideAnotherType() implements ParseMessage, Reported {}
}
