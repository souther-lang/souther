package souther.compiler;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassFile;
import java.lang.classfile.CodeElement;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.TypeCheckInstruction;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import souther.compiler.jvm.ClassFileImage;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The order a behavior's output union is generated in is the order its atoms are stated in, and no
 * consumer restates it.
 *
 * <p>A union holds its members as a set and states no order, so one is put on it where the atoms are
 * answered ({@code AtomSpace}): the members are taken in their name's order and each is descended.
 * Codegen took that answer and sorted it again by name, which is the same order only while no member
 * is itself a sum — a sum comes out of the descent in the order its cases are declared in, and
 * sorting moves it. Two answers to what order the atoms are in, and the one further from the
 * question won.
 *
 * <p>What the generated artifact says is the whole of the evidence here: the {@code permits} of the
 * sealed interface and the order its encoder dispatches in are the two places the order is written
 * down, and both are read off the classes rather than off the compiler.
 *
 * <p>The wire form does not turn on this. A value is one atom, the arms are disjoint, and each writes
 * the same tag whichever arm is tried first — which is why nothing reported the disagreement.
 */
class AUnionsGeneratedOrderIsTheOneAtomSpaceStatesTest {

    /**
     * {@code Where} is a sum of a sum, so descending it reaches {@code Domestic}, {@code Overseas},
     * {@code Draft} — an order sorting by name does not give.
     */
    private static final String MODULE = """
            module m

            data Domestic
            data Overseas
            data Region = Domestic | Overseas
            data Draft
            data Where = Region | Draft
            data NotFound

            behavior locate : (n: Int) -> Where | NotFound
            """;

    private static final List<String> STATED =
            List.of("m.NotFound", "m.Domestic", "m.Overseas", "m.Draft");

    @Test
    void theInterfacePermitsTheAtomsInTheOrderTheyAreStatedIn() throws Exception {
        assertEquals(STATED, permitsOf("locate"),
                "the union's members are its roots in name order, each descended where it is a sum");
    }

    /**
     * And the encoder dispatches in the same order.
     *
     * <p>Read as well as the {@code permits}, because they are two places the order is written down
     * and the defect was a consumer restating it. Holding only the interface leaves a sort that came
     * back inside the encoder alone unreported, which is the same shape from one step further in.
     */
    @Test
    void theEncoderDispatchesInThatOrderToo() {
        assertEquals(STATED, encoderDispatchOf("locate"));
    }

    /** And not the order sorting the atoms by name gives, which is what codegen used to write. */
    @Test
    void itIsNotTheAtomsSortedByName() {
        List<String> byName = new ArrayList<>(List.of("m.NotFound", "m.Domestic", "m.Overseas", "m.Draft"));
        byName.sort(null);
        assertEquals(List.of("m.Domestic", "m.Draft", "m.NotFound", "m.Overseas"), byName,
                "the two orders differ, so the test above is about which one is written");
    }

    private static List<String> permitsOf(String behavior) throws Exception {
        Map<String, ClassFileImage> classes = Compiler.compileModules(List.of(MODULE));
        BytesClassLoader loader = new BytesClassLoader(classes,
                AUnionsGeneratedOrderIsTheOneAtomSpaceStatesTest.class.getClassLoader());
        return Arrays.stream(loader.loadClass(Emitted.result("m", behavior)).getPermittedSubclasses())
                .map(Class::getName).toList();
    }

    /** The types the union's encoder tests, in the order it tests them. */
    private static List<String> encoderDispatchOf(String behavior) {
        Map<String, ClassFileImage> classes = Compiler.compileModules(List.of(MODULE));
        byte[] encoder = classes.get(Emitted.resultEncoder("m", behavior)).bytes();
        List<String> tested = new ArrayList<>();
        for (MethodModel method : ClassFile.of().parse(encoder).methods()) {
            if (!method.methodName().stringValue().equals("encode")) {
                continue;
            }
            method.code().ifPresent(code -> {
                for (CodeElement element : code) {
                    if (element instanceof TypeCheckInstruction check
                            && check.opcode() == java.lang.classfile.Opcode.INSTANCEOF) {
                        tested.add(check.type().asSymbol().displayName());
                    }
                }
            });
        }
        return tested.stream().map(n -> "m." + n).toList();
    }
}
