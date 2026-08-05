package souther.compiler;

import java.util.Set;

/**
 * The reserved standard-library namespace (ADR-0028, spec §stdlib): the qualifiers a call or an
 * import may write. A fact of the language, not of the loaded library — held with no dependencies
 * so the frontend and the prelude both read it without one initializing the other. {@link Prelude}
 * loads the modules behind these names and parses them through the frontend, so a constant of the
 * language that lived on either side would put the two in an initialization cycle.
 */
public final class Reserved {

    private Reserved() {}

    /** Every qualifier a call may carry: the prelude modules plus the arithmetic built-in
     *  namespaces {@code Int}/{@code Decimal} (spec §stdlib). */
    public static final Set<String> QUALIFIERS =
            Set.of("List", "String", "Map", "Set", "Bool", "Int", "Decimal", "Date", "DateTime", "Option");

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
     * from, and the identifiers an invocation names on the command line. It sits beside the other
     * facts of the language rather than in the frontend, because the CLI is not downstream of the
     * frontend and would otherwise have grown a second copy.
     *
     * <p>A string literal is canonicalized too, but separately and for its own reason: it is a value
     * that crosses a boundary, not a name (ADR-0096).
     *
     * <p>This answers which name it is and nothing else. Which characters spell it, and where they
     * are, is the other half, and a report and an editor want that half — so a name in the tree is
     * a {@link souther.compiler.ast.WrittenName}, which holds both and is where this is called from.
     */
    public static String name(String spelling) {
        return spelling == null ? null
                : java.text.Normalizer.normalize(spelling, java.text.Normalizer.Form.NFC);
    }

    /** Whether {@code moduleName} is the reserved namespace or a module inside it. The core
     *  privileges — declaring an {@code intrinsic}, declaring a {@code private let} — are the ones
     *  this answers for. */
    public static boolean isNamespace(String moduleName) {
        return moduleName != null
                && (moduleName.equals("souther") || moduleName.startsWith("souther."));
    }
}
