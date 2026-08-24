package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
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

    @Test
    void theInterfacePermitsTheAtomsInTheOrderTheyAreStatedIn() throws Exception {
        assertEquals(List.of("m.NotFound", "m.Domestic", "m.Overseas", "m.Draft"), permitsOf("locate"),
                "the union's members are its roots in name order, each descended where it is a sum");
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
        Map<String, byte[]> classes = Compiler.compileModules(List.of(MODULE));
        BytesClassLoader loader = new BytesClassLoader(classes,
                AUnionsGeneratedOrderIsTheOneAtomSpaceStatesTest.class.getClassLoader());
        return Arrays.stream(loader.loadClass(Emitted.result("m", behavior)).getPermittedSubclasses())
                .map(Class::getName).toList();
    }
}
