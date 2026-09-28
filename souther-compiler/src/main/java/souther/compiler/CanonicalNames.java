package souther.compiler;

import souther.unicode.Normalization;

/**
 * The name a spelling denotes, canonicalized to NFC.
 *
 * <p>Two spellings Unicode calls canonically equivalent are the same text, so they are the same
 * name — and a name is compared by its code units everywhere it is looked up: a declaration
 * against a reference, a case against a wire tag, a `--behavior` argument against what the module
 * declares. Leaving that to each entry point is how this went wrong twice: the tag was
 * canonicalized where it was written out while the name it came from was not, and then the name
 * was canonicalized at one entry point while four others were not.
 *
 * <p>So every place a name enters comes through here — an identifier and a type variable in a
 * source file, the module name a header-less source is given, the file stem the CLI derives one
 * from, and the identifiers an invocation names on the command line. Held here rather than beside
 * {@link Reserved}'s registry, which every one of those callers is downstream of anyway: this needs
 * {@code souther-runtime}'s {@link Normalization#nfc}, and {@code souther-fmt} reads
 * {@link Reserved#MODULES} without depending on the compiler or on {@code souther-runtime} either.
 *
 * <p>A string literal is canonicalized too, but separately and for its own reason: it is a value
 * that crosses a boundary, not a name. Both go through {@link Normalization#nfc}, the one
 * Unicode 18.0.0 NFC this language runs — not the JVM's own {@code java.text.Normalizer}, which
 * answers for whatever Unicode version this JDK shipped with.
 *
 * <p>{@link #name} answers which name it is and nothing else. Which characters spell it, and where
 * they are, is the other half, and a report and an editor want that half — so a name in the tree is
 * a {@link souther.compiler.ast.WrittenName}, which holds both and is where this is called from.
 */
public final class CanonicalNames {

    private CanonicalNames() {}

    public static String name(String spelling) {
        return spelling == null ? null : Normalization.nfc(spelling);
    }
}
