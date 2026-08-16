package souther.compiler;

import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.SoutherJvmAbi;

import java.lang.classfile.ClassFile;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;

/**
 * Class files for a test that is about which class is held where, and not about what is in one.
 *
 * <p>An emission holds the name worked out from an identity beside bytes that declare a name of
 * their own, and refuses the pair where the two differ. So a stand-in of a few bytes is no longer
 * something a test can hand it: what a test needs is a real class, declaring the name the identity
 * it is emitted for maps to.
 */
public final class EmittedBytes {

    private EmittedBytes() {}

    /** A class declaring the name {@code generated} is emitted under. */
    public static byte[] of(GeneratedClass generated) {
        return declaring(SoutherJvmAbi.nameOf(generated).binaryName());
    }

    /**
     * The same, carrying {@code field} — so that two classes of one name can be told apart by a
     * test asking which of them was kept.
     */
    public static byte[] of(GeneratedClass generated, String field) {
        return ClassFile.of().build(
                ClassDesc.of(SoutherJvmAbi.nameOf(generated).binaryName()),
                builder -> builder.withField(field, ConstantDescs.CD_int, 0));
    }

    /** A class declaring {@code binaryName}, whatever anything holds it under. */
    public static byte[] declaring(String binaryName) {
        return ClassFile.of().build(ClassDesc.of(binaryName), _ -> { });
    }
}
