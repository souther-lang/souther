package souther.compiler.meta;

import java.util.function.Function;

/**
 * What a set of compiled classes carries, for anywhere the bytes are in hand — the classes of a
 * compile in progress, a jar entry.
 *
 * <p>This decides what a lookup is told, and reads no class file to do it. Every use of the
 * class-file reader is in {@link SoutherAnnotations}, and the whole of what that class does is the
 * one call guarded here; this file imports nothing of that API, so a read hoisted out of the guard
 * has nowhere to go that is not a new import. Parsing a class file does not read it — the model is
 * lazy — so a guard around part of the reading answers only part of the malformed artifacts, which
 * is what happened while the guard was around the parse.
 *
 * <p>Under an annotation processor the same annotations are reachable through {@code Elements}
 * without the bytes, which is a second reader of the same shape.
 */
public final class ClassFileDeclarations implements PublishedClasses {

    private final Function<String, byte[]> bytesOf;

    /** Reads from whatever {@code bytesOf} returns for a binary class name; null for absent. */
    public ClassFileDeclarations(Function<String, byte[]> bytesOf) {
        this.bytesOf = bytesOf;
    }

    @Override
    public PublishedClasses.Carried of(String binaryName) {
        // Outside the guard. Whatever hands the bytes over is a caller's, and a fault in it is a
        // fault: only what is made of bytes already in hand is an answer about an artifact.
        byte[] bytes = bytesOf.apply(binaryName);
        if (bytes == null) {
            return new PublishedClasses.Carried.NoSuchClass();
        }
        try {
            return new PublishedClasses.Carried.Declared(SoutherAnnotations.in(bytes));
        } catch (IllegalArgumentException _) {
            return new PublishedClasses.Carried.UnreadableMetadata();
        }
    }
}
