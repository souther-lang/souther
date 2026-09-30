package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDesc;
import java.lang.constant.DirectMethodHandleDesc;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a character is, in the code that decides what a program means, is asked of data the language
 * carries and not of the running JDK.
 *
 * <p>{@code Character.isLetter} and its kin, and the {@code String} methods built on them, answer
 * against the Unicode version the JDK a compile or a run happens to be on carries, and most of them
 * a UTF-16 unit at a time. A rule of the language written with them moves when the JDK does: a
 * pattern one compiler reads another refuses, one behavior is two classes under two JDKs, a name
 * is cut short where it holds a character past the basic plane. The language's own answers are
 * {@code IdentifierAlphabet}, {@code UnicodeProperty}, {@code StringWhitespace}, the pattern
 * alphabet, the simple uppercase mapping and the run time's case and normalization tables, each
 * read against a version the specification fixes.
 *
 * <p>The modules are the ones whose answers are what a program means or what a module publishes:
 * the run time, the syntax and the compiler. A call left here is one whose answer does not turn on
 * a Unicode version, and the reason is written beside it; any other is a rule asking the host.
 */
class WhoMayAskTheJdkWhatACharacterIsTest {

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final List<String> MODULES =
            List.of("souther-runtime", "souther-syntax", "souther-compiler");

    /** The questions about a character the JDK answers from its own Unicode tables. */
    private static final Map<String, Set<String>> ASKING = Map.of(
            "java/lang/Character", Set.of(
                    "isLetter", "isDigit", "isLetterOrDigit", "isAlphabetic", "isWhitespace",
                    "isSpaceChar", "isUpperCase", "isLowerCase", "isTitleCase", "toUpperCase",
                    "toLowerCase", "toTitleCase", "getType", "isIdeographic", "isDefined",
                    "isMirrored", "isIdentifierIgnorable", "isUnicodeIdentifierStart",
                    "isUnicodeIdentifierPart", "isJavaIdentifierStart", "isJavaIdentifierPart",
                    "digit", "getNumericValue", "isEmoji", "isEmojiPresentation",
                    "isExtendedPictographic"),
            "java/lang/Character$UnicodeBlock", Set.of("of", "forName"),
            "java/lang/Character$UnicodeScript", Set.of("of", "forName"),
            "java/lang/String", Set.of(
                    "isBlank", "strip", "stripLeading", "stripTrailing", "toUpperCase",
                    "toLowerCase", "equalsIgnoreCase", "compareToIgnoreCase",
                    "regionMatches"));

    /**
     * The calls that stay, and why none of them is a rule of the language.
     *
     * <p>Over text the compiler spelled in ASCII, where every JDK answers alike: an enum constant's
     * or a message key's name ({@code SyntaxKind}, {@code DiagnosticCode},
     * {@code RetiredDiagnosticCode}, {@code JsonRenderer}, {@code MessageKeys},
     * {@code MessageTemplate}). About how the compiler's own documentation and reports are searched
     * and laid out, which is what a reader is shown and not what a program means: the {@code doc}
     * package, {@code AdequacyReport}, {@code ArmVocabulary}, {@code WrittenEnsures}. A precondition
     * on a value the compiler or its caller supplied, refusing nothing a source can write:
     * {@code SoutherProcessor}'s option, {@code Messages}' language tag, {@code SourceId},
     * {@code FixtureTemplate}.
     */
    private static final List<String> MAY_ASK = List.of(
            "souther/compiler/apt/SoutherProcessor#process java/lang/String.isBlank",
            "souther/compiler/cst/SyntaxKind#display java/lang/String.toLowerCase",
            "souther/compiler/diag/DiagnosticCode#docAnchor java/lang/String.toLowerCase",
            "souther/compiler/diag/JsonRenderer#render java/lang/String.toLowerCase",
            "souther/compiler/diag/Messages#namedLanguage java/lang/String.isBlank",
            "souther/compiler/diag/Messages#namesALanguage java/lang/String.isBlank",
            "souther/compiler/diag/RetiredDiagnosticCode#docAnchor java/lang/String.toLowerCase",
            "souther/compiler/diag/msg/MessageKeys#kebab java/lang/Character.isUpperCase",
            "souther/compiler/diag/msg/MessageKeys#kebab java/lang/Character.toLowerCase",
            "souther/compiler/diag/msg/MessageKeys#kebab java/lang/String.toLowerCase",
            "souther/compiler/diag/msg/MessageTemplate#isAName"
                    + " java/lang/Character.isJavaIdentifierPart",
            "souther/compiler/diag/msg/MessageTemplate#isAName"
                    + " java/lang/Character.isJavaIdentifierStart",
            "souther/compiler/doc/ApiCommand#lambda$run$0 java/lang/String.toLowerCase",
            "souther/compiler/doc/ApiCommand#printSource java/lang/String.toLowerCase",
            "souther/compiler/doc/ApiCommand#run java/lang/String.isBlank",
            "souther/compiler/doc/ApiCommand#run java/lang/String.toLowerCase",
            "souther/compiler/doc/Continuation#cut java/lang/String.isBlank",
            "souther/compiler/doc/DocCommand#run java/lang/String.isBlank",
            "souther/compiler/doc/DocCommand$Found#rendered java/lang/String.isBlank",
            "souther/compiler/doc/DocName#asWords java/lang/String.strip",
            "souther/compiler/doc/DocName#canonical java/lang/String.toLowerCase",
            "souther/compiler/doc/JapiCommand#isQualifiedName"
                    + " java/lang/Character.isJavaIdentifierPart",
            "souther/compiler/doc/JapiCommand#isQualifiedName"
                    + " java/lang/Character.isJavaIdentifierStart",
            "souther/compiler/doc/JapiCommand#lambda$indent$0 java/lang/String.strip",
            "souther/compiler/doc/LibraryDocs#lambda$snippet$2 java/lang/String.toLowerCase",
            "souther/compiler/doc/LibraryDocs#lambda$titleOf$1 java/lang/String.strip",
            "souther/compiler/doc/LibraryDocs#lines java/lang/String.strip",
            "souther/compiler/doc/LibraryDocs#on java/lang/String.strip",
            "souther/compiler/doc/LibraryDocs#rank java/lang/String.isBlank",
            "souther/compiler/doc/LibraryDocs#rank java/lang/String.toLowerCase",
            "souther/compiler/doc/LibraryDocs#snippet java/lang/String.strip",
            "souther/compiler/doc/Match$2#at java/lang/Character.isLetterOrDigit",
            "souther/compiler/doc/McpServer#serve java/lang/String.isBlank",
            "souther/compiler/doc/SourceDoc#read java/lang/String.isBlank",
            "souther/compiler/doc/SourceDoc$Collector#doc java/lang/String.isBlank",
            "souther/compiler/doc/SpecDocument#lambda$snippet$2 java/lang/String.toLowerCase",
            "souther/compiler/doc/SpecDocument#lambda$snippet$3 java/lang/String.strip",
            "souther/compiler/doc/SpecDocument#lambda$snippet$5 java/lang/String.toLowerCase",
            "souther/compiler/doc/SpecDocument#of java/lang/String.isBlank",
            "souther/compiler/doc/SpecDocument#of java/lang/String.strip",
            "souther/compiler/doc/SpecDocument#rank java/lang/String.isBlank",
            "souther/compiler/doc/SpecDocument#rank java/lang/String.toLowerCase",
            "souther/compiler/doc/SpecDocument#snippet java/lang/String.strip",
            "souther/compiler/doc/SpecIncludes#unindented java/lang/String.isBlank",
            "souther/compiler/doc/SpecIncludes#unindented java/lang/String.stripLeading",
            "souther/compiler/doc/TakenAsItStands#lines java/lang/String.isBlank",
            "souther/compiler/doc/TakenAsItStands#lines java/lang/String.strip",
            "souther/compiler/partition/FixtureTemplate#<init> java/lang/String.isBlank",
            "souther/compiler/report/AdequacyReport#gathered java/lang/String.stripTrailing",
            "souther/compiler/report/AdequacyReport#human java/lang/String.toLowerCase",
            "souther/compiler/report/AdequacyReport#word java/lang/String.toLowerCase",
            "souther/compiler/report/ArmVocabulary#label java/lang/String.toLowerCase",
            "souther/compiler/report/WrittenEnsures#indentOf java/lang/Character.isWhitespace",
            "souther/compiler/source/SourceId#<init> java/lang/String.isBlank");

    @Test
    void noRuleOfTheLanguageAsksTheJdkWhatACharacterIs() {
        assertEquals(MAY_ASK, asking(),
                "a character is classified by the data the language carries, against the version"
                        + " the specification fixes, and not by the running JDK's tables");
    }

    private static List<String> asking() {
        Set<String> out = new TreeSet<>();
        for (String module : MODULES) {
            for (ClassModel each : COMPILED.classesOf(COMPILED.module(module))) {
                for (MethodModel method : each.methods()) {
                    for (CodeModel code : method.code().stream().toList()) {
                        String at = each.thisClass().asInternalName() + "#"
                                + method.methodName().stringValue() + " ";
                        for (CodeElement element : code) {
                            if (element instanceof InvokeInstruction invoke) {
                                asked(invoke.owner().asInternalName(), invoke.name().stringValue(),
                                        at, out);
                            }
                            // A method reference, `String::isBlank`, is a handle handed to the
                            // bootstrap of a call site rather than a call.
                            if (element instanceof InvokeDynamicInstruction dynamic) {
                                for (ConstantDesc argument : dynamic.bootstrapArgs()) {
                                    if (argument instanceof DirectMethodHandleDesc handle) {
                                        asked(internalName(handle.owner()), handle.methodName(),
                                                at, out);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return new ArrayList<>(out);
    }

    private static void asked(String owner, String name, String at, Set<String> out) {
        if (ASKING.getOrDefault(owner, Set.of()).contains(name)) {
            out.add(at + owner + "." + name);
        }
    }

    /** {@code Ljava/lang/String;} as {@code java/lang/String}. */
    private static String internalName(ClassDesc type) {
        String descriptor = type.descriptorString();
        return descriptor.substring(1, descriptor.length() - 1);
    }
}
