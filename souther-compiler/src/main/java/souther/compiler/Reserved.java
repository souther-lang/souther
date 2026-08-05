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

    /** Whether {@code moduleName} is the reserved namespace or a module inside it. The core
     *  privileges — declaring an {@code intrinsic}, declaring a {@code private let} — are the ones
     *  this answers for. */
    public static boolean isNamespace(String moduleName) {
        return moduleName != null
                && (moduleName.equals("souther") || moduleName.startsWith("souther."));
    }
}
