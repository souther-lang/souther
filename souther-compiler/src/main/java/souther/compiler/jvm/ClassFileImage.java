package souther.compiler.jvm;

import java.nio.charset.StandardCharsets;
import java.util.Objects;

/**
 * A class file this compilation produced, held as what its bytes say rather than as which array they
 * arrived in.
 *
 * <p>Every question that answers with a module's classes answers with these. A class file is its
 * bytes: two compiles that emitted the same class emitted the same thing, and what lets a store stop
 * work when a module comes out the same is holding them as something that says so. An array says
 * which array it is however its elements compare, so an answer holding one can never equal its own
 * recomputation — and a wrapper with an array inside is that same place one member further down.
 *
 * <p><b>Why the bytes are carried as a string.</b> Three things are wanted at once: the language has
 * to settle what one of these means, the carrier has to be immutable, and the round trip has to be
 * exact. ISO-8859-1 maps all 256 octets onto U+0000&ndash;U+00FF and back, one for one, so a string
 * built this way holds the bytes and nothing else. What that buys is a value whose equality is every
 * octet — not a digest, so nothing here rests on two different class files being unable to collide.
 * How much room it takes is the runtime's business and no part of why it is written this way.
 *
 * <p>Copied on the way in and on the way out. A caller that goes on writing into the array it handed
 * over does not change what this holds, and one that writes into the array it is given changes
 * nothing but its own copy. That is what a value is, and it is what the {@code byte[]} this replaces
 * never was: a module's classes were handed to every reader as arrays anyone could write into.
 *
 * <p>Named for what it is and not {@code ClassFile}, which is what the language calls the API that
 * reads and writes one ({@link java.lang.classfile.ClassFile}). That one is a way of parsing bytes;
 * this one is the bytes.
 */
public final class ClassFileImage {

    /** The octets, one per character. */
    private final String contents;

    private ClassFileImage(String contents) {
        this.contents = contents;
    }

    /** The class file in {@code bytes}, which this takes a copy of. */
    public static ClassFileImage of(byte[] bytes) {
        Objects.requireNonNull(bytes, "a class file is its bytes");
        return new ClassFileImage(new String(bytes, StandardCharsets.ISO_8859_1));
    }

    /**
     * The bytes, as a fresh array each time.
     *
     * <p>For handing to something that takes octets and nothing else — {@code defineClass}, a file,
     * an archive. A reader that keeps what comes back is keeping an array again, which is the whole
     * of what this type exists to stop; what is kept is one of these.
     */
    public byte[] bytes() {
        return contents.getBytes(StandardCharsets.ISO_8859_1);
    }

    /** How many bytes the class file is. */
    public int size() {
        return contents.length();
    }

    @Override
    public boolean equals(Object other) {
        return this == other
                || other instanceof ClassFileImage that && contents.equals(that.contents);
    }

    @Override
    public int hashCode() {
        return contents.hashCode();
    }

    /** What it is and how big, without the bytes: nothing reads a class file by looking at it. */
    @Override
    public String toString() {
        return "a class file of " + contents.length() + " bytes";
    }
}
