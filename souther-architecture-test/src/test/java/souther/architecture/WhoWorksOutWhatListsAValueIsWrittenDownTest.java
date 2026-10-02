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
 * Which methods work out for themselves which enumerations list a unit value.
 *
 * <p>Two ways do it: the capability that walks the value's module each time it is asked
 * ({@code EnumerationListings#asWritten}), and the table of a whole module
 * ({@code TypeOps#enumerationsListing}). Each reads every sum of the module, so a reader holding the
 * first and ordering many values pays the module for every one of them — and the compilation
 * already holds the answer once for each module ({@code Shapes#enumerationListings}).
 *
 * <p>So the methods that make one are written down. What entitles one is that it has no compilation
 * to ask, or that it is making what a declaration says and has taken that declaration out of what
 * the compilation's answer would read, or that it records what it reads on its own terms.
 *
 * <p>Read off the compiled classes, per method and per overload ({@link AMethod}), and a method
 * handed over to be called later is a caller.
 */
class WhoWorksOutWhatListsAValueIsWrittenDownTest {

    private static final String CHECK = "souther/compiler/check/";

    private static final String CODEGEN = "souther/compiler/codegen/";

    private static final String QUERY = "souther/compiler/query/";

    private static final String LISTINGS = CHECK + "EnumerationListings";

    private static final String TYPE_OPS = CHECK + "TypeOps";

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final String THE_WALK = LISTINGS + "#asWritten";

    private static final String THE_TABLE = TYPE_OPS + "#enumerationsListing";

    private static final String SYMBOLS = "L" + CHECK + "Symbols;";

    private static final String KINDS = "L" + CHECK + "DeclarationKinds;";

    private static final String PUBLISHED = "L" + CHECK + "PublishedDeclarations;";

    private static final String ACCESS = "L" + CHECK + "DeclarationAccess;";

    /**
     * Every method that works it out, and the way it does.
     *
     * <p>The answer handed to a reading made of a scope alone, and to one making what a declaration
     * says. The emitter, which is handed no answer of the compilation's. The compilation's own
     * answer for a module. And the linkage of a module, which records what it reads as what its
     * classes are built against.
     */
    private static final List<String> WORKING_IT_OUT = List.of(
            row(CHECK + "DeclarationAccess", "asWritten",
                    "(" + SYMBOLS + PUBLISHED + KINDS + ")" + ACCESS, THE_WALK),
            row(CHECK + "DeclarationAccess", "saying", "(" + PUBLISHED + SYMBOLS + ")" + ACCESS,
                    THE_WALK),
            row(CODEGEN + "BodyGen", "context", "()L" + CHECK + "CheckContext;", THE_WALK),
            row(CODEGEN + "ValueClassGen", "orderOfWrapped",
                    "(Lsouther/compiler/types/Type;)L" + CHECK + "Ordering;", THE_WALK),
            QUERY + "Linkages#orders, in a lambda -> " + THE_TABLE,
            row(QUERY + "Shapes$EnumerationsListingIn", "compute",
                    "(L" + QUERY + "Db;)L" + QUERY + "Answer;", THE_TABLE));

    private static String row(String owner, String name, String descriptor, String way) {
        return AMethod.of(owner, name, descriptor) + " -> " + way;
    }

    @Test
    void everyMethodThatWorksOutWhatListsAValueIsWrittenDown() {
        Set<String> found = workingItOut();
        assertEquals(WORKING_IT_OUT, List.copyOf(found),
                () -> "the methods that work out which enumerations list a value are not the ones"
                        + " written down.\n  found:\n    " + String.join("\n    ", found)
                        + "\nTake the compilation's answer (Shapes#enumerationListings, handed in a"
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
        if (LISTINGS.equals(owner) && name.equals("asWritten")) {
            return Optional.of(THE_WALK);
        }
        if (TYPE_OPS.equals(owner) && name.equals("enumerationsListing")) {
            return Optional.of(THE_TABLE);
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
