package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Generated classes target Java 25 (spec 19.1).
 *
 * <p>Without this the version follows whatever JDK runs the compiler, which is silent and
 * environment-dependent: building on a newer JDK produces classes the target runtime cannot
 * load, and two developers emit mutually incompatible artifacts. The pin is what makes the floor a
 * decision rather than a property of whoever ran the build.
 */
class CompileClassVersionTest {

    private static final String MODULE = """
            module demo
            import String ( length )

            data 会員ID = { value: String } invariant length(value) > 0
            data Contact = EmailContact | PhoneContact
            data EmailContact = { email: String }
            data PhoneContact = { phone: String }
            data Mark

            behavior 名を取る : (c: EmailContact) -> 会員ID constructs 会員ID

            let 名を取る (c) = 会員ID { value = c.email }
            """;

    /** major 69 is Java 25. Pinned, so it stays put when the JDK running the build moves on. */
    private static final int JAVA_25 = 69;

    private static int majorVersion(byte[] cls) {
        // u4 magic, u2 minor, u2 major
        return ((cls[6] & 0xff) << 8) | (cls[7] & 0xff);
    }

    @Test
    void everyGeneratedClassTargetsJava25() {
        Map<String, byte[]> classes = Compiler.compile(MODULE);
        for (Map.Entry<String, byte[]> e : classes.entrySet()) {
            assertEquals(JAVA_25, majorVersion(e.getValue()),
                    e.getKey() + " must target Java 25, not the JDK that built it");
        }
    }

    @Test
    void theCompilerEmitsDataDecodersAndBehaviorsAlike() {
        Map<String, byte[]> classes = Compiler.compile(MODULE);
        // guards the test above against silently covering an empty or tiny set
        assertEquals(true, classes.size() >= 10, "expected the whole module's output, got " + classes.keySet());
    }
}
