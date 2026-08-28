package souther.compiler.codegen;

import org.junit.jupiter.api.Test;

import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.SoutherJvmAbi;

import java.lang.classfile.ClassFile;
import java.lang.constant.ClassDesc;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a module ships is a map from a name to the class under it, and a loader reads the name off
 * the map while the JVM reads it off the bytes. Where the two differ, the class that was written is
 * the one nobody asked for and the one that was asked for is missing — which arrives as a linkage
 * error against a third module, if it arrives at all.
 *
 * <p>An emission holds the identity it was made for, so the name is worked out from that identity
 * once. The bytes are built by a second walk that could work it out again, and the way that goes
 * wrong is a walk answering from a table keyed by a spelling two declarations share. This is where
 * the two answers are held against each other.
 */
class AClassIsHeldUnderTheNameItDeclaresTest {

    /** A class file declaring {@code binaryName} and nothing else. */
    private static byte[] declaring(String binaryName) {
        return ClassFile.of().build(ClassDesc.of(binaryName), _ -> { });
    }

    @Test
    void bytesDeclaringAnotherClassAreRefused() {
        Emissions emissions = new Emissions("app.twin");
        GeneratedClass held = new GeneratedClass.BehaviorInterface("app.twin", "f");

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> emissions.put(held, declaring("app.a.F")));

        assertTrue(refused.getMessage().contains("app.a.F"), refused.getMessage());
        assertTrue(refused.getMessage().contains(SoutherJvmAbi.nameOf(held).binaryName()),
                refused.getMessage());
    }

    @Test
    void aRewriteThatRenamesTheClassIsRefused() {
        Emissions emissions = new Emissions("app.twin");
        GeneratedClass held = new GeneratedClass.BehaviorInterface("app.twin", "f");
        emissions.put(held, declaring(SoutherJvmAbi.nameOf(held).binaryName()));

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> emissions.rewrite(held, _ -> declaring("app.a.F")));

        assertTrue(refused.getMessage().contains("app.a.F"), refused.getMessage());
    }

    @Test
    void bytesDeclaringTheNameTheyAreHeldUnderAreKept() {
        Emissions emissions = new Emissions("app.twin");
        GeneratedClass held = new GeneratedClass.BehaviorInterface("app.twin", "f");
        String name = SoutherJvmAbi.nameOf(held).binaryName();

        emissions.put(held, declaring(name));

        assertEquals(java.util.Set.of(name), emissions.seal().keySet());
    }
}
