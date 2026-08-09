package souther.compiler.diag.msg;

import souther.compiler.diag.DiagnosticCode;

/** What an `import` line is told: a name the module it names does not publish, and a name that
 * would stand for two things here. */
public sealed interface ImportMessage extends Message {

    /** The module publishes no operation of that name. */
    @Code(DiagnosticCode.E1506)
    record NameIsNotAStandardLibraryFunction(String name, String module) implements ImportMessage, Reported {}

    /** The imported name is also declared here, so it would stand for two things. */
    @Code(DiagnosticCode.E1508)
    record ImportedNameCollidesWithADeclaration(String name) implements ImportMessage, Reported {}

    /** What to do about a name that would stand for two things. */
    record RenameOrQualifyTheCollidingName() implements ImportMessage, Supporting {}

    /** Two modules publish the name, so importing both leaves it saying neither. */
    @Code(DiagnosticCode.E1508)
    record NameIsPublishedByTwoModules(String name, String publishedBy, String andBy)
            implements ImportMessage, Reported {}
}
