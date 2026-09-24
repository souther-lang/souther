package souther.compiler.meta;

/**
 * Where a published behavior's signature comes from: a declaration its module wrote, or the stages
 * of a {@code >->} composition.
 *
 * <p>Carried beside the signature because the signature cannot say it. What travels is source, and
 * a composition has no source for what it takes — it declares stages, which stay with the module
 * that wrote them (ADR-0063) — so the signature its stages compute is written out as a declaration
 * would be, with parameter names made up for the parser. Read back without this, those names are a
 * declaration nobody wrote, and the behavior is one that declared parameters: a reader would call
 * it by name where a composition is composed with, and name inputs the model never named.
 */
enum PublishedSignature {

    /** The behavior wrote this signature, parameter names and all. */
    DECLARED,

    /** A composition: the signature is what its stages compute, and its parameter names were made
     *  up to write it out. */
    COMPOSED;

    /** The word the metadata carries for it. */
    String written() {
        return switch (this) {
            case DECLARED -> "declared";
            case COMPOSED -> "composed";
        };
    }

    /** The one that word names, or null where it names none. */
    static PublishedSignature readingWritten(String word) {
        for (PublishedSignature each : values()) {
            if (each.written().equals(word)) {
                return each;
            }
        }
        return null;
    }
}
