package souther.compiler.codegen;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What a module emits holds one class under one binary name, and says so when it does not.
 *
 * <p>A plain map answers a second write of a name by keeping the second and dropping the first, so
 * the compile succeeded and the artifact set was a class short — which arrived, much later, as a
 * linkage error against whatever had gone missing. No source reaches that today: {@code $} is not
 * written in a name, so a model cannot spell a generated class's name, and a declaration that would
 * emit a class another declaration already has is refused where it is declared. Both of those are
 * rules about names; this is about the writing, and it is what a naming scheme changed later runs
 * into instead of the silence.
 */
class TwoClassesUnderOneNameAreNotOneClassTest {

    @Test
    void asecondClassUnderAWrittenNameIsRefused() {
        Map<String, byte[]> out = new Backend.OneClassPerName();
        out.put("demo.A", new byte[] {1});
        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> out.put("demo.A", new byte[] {2}));
        assertEquals(List.of("demo.A"), List.copyOf(out.keySet()),
                "the class already written stays the one that is written");
        assertEquals(1, out.get("demo.A")[0], "and it is not replaced on the way out");
        org.junit.jupiter.api.Assertions.assertTrue(refused.getMessage().contains("demo.A"),
                "the refusal names the class: " + refused.getMessage());
    }

    /** And through the door a whole set of classes arrives by, which is how the classes compiled for
     *  escaping lambdas are added. */
    @Test
    void andSoIsOneArrivingWithOthers() {
        Map<String, byte[]> out = new Backend.OneClassPerName();
        out.put("demo.A", new byte[] {1});
        Map<String, byte[]> more = new LinkedHashMap<>();
        more.put("demo.B", new byte[] {2});
        more.put("demo.A", new byte[] {3});
        assertThrows(IllegalStateException.class, () -> out.putAll(more));
    }

    /** The control: distinct names are written, in the order they were written in. */
    @Test
    void andEveryOtherNameIsWritten() {
        Map<String, byte[]> out = new Backend.OneClassPerName();
        out.put("demo.A", new byte[] {1});
        out.putAll(Map.of("demo.A$Enc", new byte[] {2}));
        out.put("demo.B", new byte[] {3});
        assertEquals(List.of("demo.A", "demo.A$Enc", "demo.B"), List.copyOf(out.keySet()));
    }
}
