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
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Which methods read the cases a sum lists off the declarations themselves, rather than asking the
 * answer they were handed.
 *
 * <p>Two ways do it: off a scope's declarations ({@code ListedCases#asWritten}) and off whatever
 * answers a declaration for an address ({@code ListedCases#readOff}). A reader handed a
 * {@code DeclarationAccess} holds the answer already — the compilation's, or the one read off the
 * scope it was built from — and a reader that works it out again beside that has two answers to the
 * one question, read at whichever stage the scope it holds happens to be.
 *
 * <p>So the methods that do it are written down, and what entitles one is that it makes the answer
 * every other reader is handed, or that it records what it reads as what it is built against — an
 * answer of the compilation's read past the recording would leave a module saying it was built
 * against less than it read.
 *
 * <p>Read off the compiled classes, per method and per overload ({@link AMethod}), and a method
 * handed over to be called later is a caller.
 */
class WhoReadsWhatASumListsOffTheDeclarationsIsWrittenDownTest {

    private static final String CHECK = "souther/compiler/check/";

    private static final String CODEGEN = "souther/compiler/codegen/";

    private static final String QUERY = "souther/compiler/query/";

    private static final String LISTED_CASES = CHECK + "ListedCases";

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final String OFF_A_SCOPE = LISTED_CASES + "#asWritten";

    private static final String OFF_DECLARATIONS = LISTED_CASES + "#readOff";

    private static final String SYMBOLS = "L" + CHECK + "Symbols;";

    private static final String KINDS = "L" + CHECK + "DeclarationKinds;";

    private static final String PUBLISHED = "L" + CHECK + "PublishedDeclarations;";

    private static final String ACCESS = "L" + CHECK + "DeclarationAccess;";

    /**
     * Every method that reads it off the declarations, and the way it does.
     *
     * <p>The declaration questions read off a scope, for a reading made of a scope alone, which is
     * what a reader of that scope is handed. Reading off a scope, which is reading off what it
     * answers for an address. The emitter's context, which is handed no answer of the compilation's
     * and records what it reads. The linkage of a module, which reads through what records it as
     * what the module's classes are built against. And the compilation's own answer for a sum.
     */
    private static final List<String> READING_IT = List.of(
            row(CHECK + "DeclarationAccess", "asWritten",
                    "(" + SYMBOLS + PUBLISHED + KINDS + ")" + ACCESS, OFF_A_SCOPE),
            row(LISTED_CASES, "asWritten", "(" + SYMBOLS + ")L" + LISTED_CASES + ";",
                    OFF_DECLARATIONS),
            row(CODEGEN + "CodegenContext", "<init>",
                    "(Ljava/lang/String;L" + CHECK + "DerivedSymbols;" + PUBLISHED + KINDS + "L"
                            + CHECK + "NewtypeInners;Lsouther/compiler/core/KernelSignatures;"
                            + "Ljava/util/Map;Ljava/util/Map;Ljava/util/Set;Ljava/util/Map;"
                            + "Lsouther/compiler/diag/SourceLayouts;"
                            + "Lsouther/compiler/diag/QuotedFrom;L" + CODEGEN + "LinkageReader;)V",
                    OFF_A_SCOPE),
            row(QUERY + "Linkages$Provided", "compute",
                    "(L" + QUERY + "Db;)L" + QUERY + "Answer;", OFF_A_SCOPE),
            row(QUERY + "Names$CasesListedBy", "compute",
                    "(L" + QUERY + "Db;)L" + QUERY + "Answer;", OFF_DECLARATIONS));

    private static String row(String owner, String name, String descriptor, String way) {
        return AMethod.of(owner, name, descriptor) + " -> " + way;
    }

    @Test
    void everyMethodThatReadsWhatASumListsOffTheDeclarationsIsWrittenDown() {
        Set<String> found = readingIt();
        assertEquals(READING_IT.stream().sorted().toList(), List.copyOf(found),
                () -> "the methods that read what a sum lists off the declarations are not the"
                        + " ones written down.\n  found:\n    " + String.join("\n    ", found)
                        + "\nAsk the DeclarationAccess this reader was handed, or say here why"
                        + " this method reads it off the declarations.");
    }

    private static Set<String> readingIt() {
        Set<String> found = new TreeSet<>();
        for (ClassModel model : COMPILED.all()) {
            for (MethodModel method : model.methods()) {
                for (Instruction instruction : instructionsOf(method)) {
                    wayOf(instruction).ifPresent(way -> found.add(
                            methodOf(model, method) + " -> " + way));
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

    /** The way an instruction reads it, if it names one: by calling it, or by handing it over. */
    private static Optional<String> wayOf(Instruction instruction) {
        return switch (instruction) {
            case InvokeInstruction call -> aWay(call.owner().name().stringValue(),
                    call.name().stringValue());
            case InvokeDynamicInstruction handed -> {
                for (LoadableConstantEntry each : handed.invokedynamic().bootstrap().arguments()) {
                    if (each instanceof MethodHandleEntry handle) {
                        MemberRefEntry member = handle.reference();
                        Optional<String> way = aWay(member.owner().name().stringValue(),
                                member.name().stringValue());
                        if (way.isPresent()) {
                            yield way;
                        }
                    }
                }
                yield Optional.empty();
            }
            default -> Optional.empty();
        };
    }

    private static Optional<String> aWay(String owner, String name) {
        if (LISTED_CASES.equals(owner) && name.equals("asWritten")) {
            return Optional.of(OFF_A_SCOPE);
        }
        if (LISTED_CASES.equals(owner) && name.equals("readOff")) {
            return Optional.of(OFF_DECLARATIONS);
        }
        return Optional.empty();
    }

    private static List<Instruction> instructionsOf(MethodModel method) {
        Optional<CodeModel> code = method.code();
        return code.map(each -> each.elementList().stream()
                .filter(Instruction.class::isInstance)
                .map(Instruction.class::cast)
                .toList()).orElse(List.of());
    }
}
