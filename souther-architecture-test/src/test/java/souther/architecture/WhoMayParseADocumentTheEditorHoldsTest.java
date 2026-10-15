package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeModel;
import java.lang.classfile.Instruction;
import java.lang.classfile.MethodModel;
import java.lang.classfile.constantpool.LoadableConstantEntry;
import java.lang.classfile.constantpool.MemberRefEntry;
import java.lang.classfile.constantpool.MethodHandleEntry;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Which methods of the language server parse a text, and which of them make the reading every
 * question about a document shares.
 *
 * <p>A document is parsed once for each text it has, and every question asked of it reads that one
 * parse — its tree, its lines and columns, what it imports. A method that parsed for itself beside
 * that reading answers the same question again for each request, and one inside a loop answers it
 * again for each place it is after: a hint for every parameter, a location for every use. Nothing
 * fails when that happens, and a count of the shared readings stays where it was, because the
 * reading that is counted was never asked.
 *
 * <p>So the methods are written down, in two halves. Those that call the parser, or something that
 * calls it on a text it is handed: the reading itself, and the probe that tries a repaired text
 * against the parser to find out whether it is a source. And those that make a reading: the one
 * place it is kept by document, and the one that reads a text with no document to keep it under.
 *
 * <p>Over the server's own classes and no others. The compiler parses what it compiles, and that is
 * the compiler's to say; what this holds is that the editor does not parse beside it.
 *
 * <p>Read off the compiled classes, per method and per overload ({@link AMethod}), and a method
 * handed over to be called later is a caller.
 */
class WhoMayParseADocumentTheEditorHoldsTest {

    private static final String LSP = "souther/lsp/";

    private static final String ANALYSIS = LSP + "analysis/";

    private static final String ANALYZER = ANALYSIS + "Analyzer";

    private static final String READING = ANALYZER + "$Reading";

    private static final String PROBE = ANALYSIS + "SemanticProbe";

    private static final String CST = "souther/compiler/cst/";

    private static final String PARSER = CST + "CstParser";

    private static final String LAYOUT = CST + "SourceLayout";

    private static final String FRONTEND = "souther/compiler/frontend/CstFrontend";

    private static final String STRING = "Ljava/lang/String;";

    private static final String SOURCE_ID = "Lsouther/compiler/source/SourceId;";

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final String PARSE = AMethod.of(PARSER, "parse",
            "(" + STRING + ")L" + PARSER + "$Result;");

    private static final String READ = AMethod.of(READING, "of", "(" + STRING + SOURCE_ID
            + "ZLjava/util/function/BiFunction;Ljava/lang/Runnable;)L" + READING + ";");

    /**
     * Every method that parses a text it is handed, and what it calls to.
     *
     * <p>The reading parses its text when it is made, and parses it again where its tree is asked
     * for and it kept none: a document the editor has closed, which keeps the small facts and lets
     * the tree go, or a parse that did not finish, which meets the same failure again. It builds
     * what the text imports the first time that is asked. The probe parses each repair it tries,
     * because a repair is one only if it parses.
     */
    private static final List<String> PARSING = List.of(
            READ + " -> " + PARSE,
            AMethod.of(READING, "root", "()Lsouther/compiler/cst/SyntaxNode;") + " -> " + PARSE,
            AMethod.of(READING, "importsOf", "(" + STRING + ")Ljava/util/Optional;") + " -> "
                    + AMethod.of(FRONTEND, "parse",
                            "(" + STRING + STRING + ")Lsouther/compiler/ast/Ast$Module;"),
            AMethod.of(PROBE, "parses", "(" + STRING + ")Lsouther/compiler/cst/SyntaxNode;")
                    + " -> " + PARSE);

    /**
     * Every method that makes a reading.
     *
     * <p>Two. The analyzer keeps one by document, open or closed, and makes it where the text it
     * holds is not the text it is asked about or where an open document needs back the tree its
     * closed reading let go. Beside that, the reading of a text with no document, which every entry
     * point handed one asks for and nothing keeps.
     */
    private static final List<String> READING_ONE = List.of(
            AMethod.of(ANALYZER, "readingOf", "(" + STRING + STRING + "Z)L" + READING + ";")
                    + " -> " + READ,
            AMethod.of(ANALYZER, "readingOf", "(" + STRING + ")L" + READING + ";") + " -> " + READ);

    @Test
    void everyMethodOfTheServerThatParsesATextIsWrittenDown() {
        Set<String> found = callers(WhoMayParseADocumentTheEditorHoldsTest::parses);
        assertEquals(PARSING.stream().sorted().toList(), List.copyOf(found),
                () -> "the methods of the server that parse a text are not the ones written"
                        + " down.\n  found:\n    " + String.join("\n    ", found)
                        + "\nAsk the reading of the document — its tree, its layout, its lines —"
                        + " rather than parsing the text again.");
    }

    @Test
    void everyMethodOfTheServerThatMakesAReadingIsWrittenDown() {
        // Every overload of it, so a reading made by a way written later is one of these too.
        Set<String> found = callers((owner, name, descriptor) ->
                READING.equals(owner) && name.equals("of"));
        assertEquals(READING_ONE.stream().sorted().toList(), List.copyOf(found),
                () -> "the methods of the server that make a reading are not the ones written"
                        + " down.\n  found:\n    " + String.join("\n    ", found)
                        + "\nA reading made beside the one kept for the document is a parse of"
                        + " its own; ask the analyzer's reading of the document instead.");
    }

    /**
     * Whether calling the method {@code name} of {@code owner} parses the text it is handed: the
     * parser, a layout made of a text rather than of a tree already built, and the front end, every
     * entry of which starts with a parse.
     */
    private static boolean parses(String owner, String name, String descriptor) {
        return (PARSER.equals(owner) && name.equals("parse"))
                || (LAYOUT.equals(owner) && name.equals("of") && descriptor.startsWith("(" + STRING))
                || (FRONTEND.equals(owner) && name.startsWith("parse"));
    }

    @FunctionalInterface
    private interface Callee {
        boolean is(String owner, String name, String descriptor);
    }

    /** Every method of the server that calls or hands over a callee {@code wanted} names, as the
     *  method and the callee. */
    private static Set<String> callers(Callee wanted) {
        Set<String> found = new TreeSet<>();
        for (ClassModel model : COMPILED.all()) {
            if (!model.thisClass().asInternalName().startsWith(LSP)) {
                continue;
            }
            for (MethodModel method : model.methods()) {
                for (Instruction instruction : instructionsOf(method)) {
                    for (MemberRefEntry callee : calleesOf(instruction)) {
                        String owner = callee.owner().name().stringValue();
                        String name = callee.name().stringValue();
                        String descriptor = callee.type().stringValue();
                        if (wanted.is(owner, name, descriptor)) {
                            found.add(methodOf(model, method) + " -> "
                                    + AMethod.of(owner, name, descriptor));
                        }
                    }
                }
            }
        }
        return found;
    }

    /**
     * The method, or for the body of a lambda the method it is written in. The number javac gives
     * a lambda is its own choice and moves when another lambda is written above it; the method it
     * is written in is the author's.
     */
    private static String methodOf(ClassModel model, MethodModel method) {
        String name = method.methodName().stringValue();
        if (name.startsWith("lambda$")) {
            String writtenIn = name.substring("lambda$".length(), name.lastIndexOf('$'));
            return model.thisClass().asInternalName() + "#" + writtenIn + ", in a lambda";
        }
        return AMethod.of(model, method);
    }

    /** What an instruction calls, or hands over to be called. */
    private static List<MemberRefEntry> calleesOf(Instruction instruction) {
        List<MemberRefEntry> out = new ArrayList<>();
        switch (instruction) {
            case InvokeInstruction call -> out.add(call.method());
            case InvokeDynamicInstruction handed -> {
                for (LoadableConstantEntry each : handed.invokedynamic().bootstrap().arguments()) {
                    if (each instanceof MethodHandleEntry handle) {
                        out.add(handle.reference());
                    }
                }
            }
            default -> { }
        }
        return out;
    }

    private static List<Instruction> instructionsOf(MethodModel method) {
        Optional<CodeModel> code = method.code();
        return code.map(each -> each.elementList().stream()
                .filter(Instruction.class::isInstance)
                .map(Instruction.class::cast)
                .toList()).orElse(List.of());
    }
}
