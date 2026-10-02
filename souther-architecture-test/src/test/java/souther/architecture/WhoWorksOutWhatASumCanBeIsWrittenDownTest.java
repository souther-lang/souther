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
 * Which methods work out for themselves what a value of a sum can be.
 *
 * <p>Two ways do it: the capability that descends a sum each time it is asked
 * ({@code SumCases#asWritten}), and the descent it is made of ({@code AtomSpace#leavesUnder}). Each
 * reads what every case of the sum is, so a reader holding the capability and ordering many values
 * of an enumeration pays for every case of it each time — and the compilation already holds the
 * answer once for each sum ({@code Shapes#sumCases}, handed in a {@code DeclarationAccess}). The
 * declaration questions read off a scope ({@code DeclarationAccess#asWritten}) make one, and are
 * watched by {@code WhoWorksOutWhatListsAValueIsWrittenDownTest}; they are written here as the one
 * method that makes it for them.
 *
 * <p>So the methods that make one are written down. What entitles one is that it is the
 * compilation's answer itself, that it has no compilation to ask, or that it records what it reads
 * as what it is built against — an answer of the compilation's read past the recording would leave
 * a module saying it was built against less than it read.
 *
 * <p>Read off the compiled classes, per method and per overload ({@link AMethod}), and a method
 * handed over to be called later is a caller.
 */
class WhoWorksOutWhatASumCanBeIsWrittenDownTest {

    private static final String CHECK = "souther/compiler/check/";

    private static final String CODEGEN = "souther/compiler/codegen/";

    private static final String QUERY = "souther/compiler/query/";

    private static final String SUM_CASES = CHECK + "SumCases";

    private static final String ATOM_SPACE = CHECK + "AtomSpace";

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final String THE_WALK = SUM_CASES + "#asWritten";

    private static final String THE_DESCENT = ATOM_SPACE + "#leavesUnder";

    private static final String SYMBOLS = "L" + CHECK + "Symbols;";

    private static final String KINDS = "L" + CHECK + "DeclarationKinds;";

    private static final String PUBLISHED = "L" + CHECK + "PublishedDeclarations;";

    private static final String ACCESS = "L" + CHECK + "DeclarationAccess;";

    /**
     * Every method that works it out, and the way it does.
     *
     * <p>The declaration questions read off a scope, for a reading made of a scope alone. The
     * capability, which is the descent asked of one sum. The emitter's context, which is handed no
     * answer of the compilation's and records what it reads. The linkage of a module, which reads
     * through what records it as what the module's classes are built against. And the compilation's
     * own answer for a sum.
     */
    private static final List<String> WORKING_IT_OUT = List.of(
            row(CHECK + "DeclarationAccess", "asWritten",
                    "(" + SYMBOLS + PUBLISHED + KINDS + ")" + ACCESS, THE_WALK),
            CHECK + "SumCases#asWritten, in a lambda -> " + THE_DESCENT,
            row(CODEGEN + "CodegenContext", "<init>",
                    "(Ljava/lang/String;L" + CHECK + "DerivedSymbols;" + PUBLISHED + KINDS + "L"
                            + CHECK + "NewtypeInners;Lsouther/compiler/core/KernelSignatures;"
                            + "Ljava/util/Map;Ljava/util/Map;Ljava/util/Set;Ljava/util/Map;"
                            + "Lsouther/compiler/diag/SourceLayouts;"
                            + "Lsouther/compiler/diag/QuotedFrom;L" + CODEGEN + "LinkageReader;)V",
                    THE_WALK),
            row(QUERY + "Linkages$Provided", "compute",
                    "(L" + QUERY + "Db;)L" + QUERY + "Answer;", THE_WALK),
            row(QUERY + "Shapes$SumCasesOf", "compute",
                    "(L" + QUERY + "Db;)L" + QUERY + "Answer;", THE_WALK));

    private static String row(String owner, String name, String descriptor, String way) {
        return AMethod.of(owner, name, descriptor) + " -> " + way;
    }

    @Test
    void everyMethodThatWorksOutWhatASumCanBeIsWrittenDown() {
        Set<String> found = workingItOut();
        assertEquals(WORKING_IT_OUT, List.copyOf(found),
                () -> "the methods that work out what a value of a sum can be are not the ones"
                        + " written down.\n  found:\n    " + String.join("\n    ", found)
                        + "\nTake the compilation's answer (Shapes#sumCases, handed in a"
                        + " DeclarationAccess), or say here why this method works it out.");
    }

    private static Set<String> workingItOut() {
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

    /** The way an instruction works it out, if it names one: by calling it, or by handing it over. */
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
        if (SUM_CASES.equals(owner) && name.equals("asWritten")) {
            return Optional.of(THE_WALK);
        }
        if (ATOM_SPACE.equals(owner) && name.equals("leavesUnder")) {
            return Optional.of(THE_DESCENT);
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
