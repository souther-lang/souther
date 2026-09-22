package souther.compiler;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * The reserved standard-library namespace (ADR-0028, spec §stdlib): the qualifiers a call or an
 * import may write. A fact of the language, not of the loaded library — held with no dependencies
 * so the frontend and the standard library both read it without one initializing the other. The
 * loader ({@code check.StdlibLoader}) parses the modules behind these names through the frontend,
 * so a constant of the language that lived on either side would put the two in an initialization
 * cycle. Canonicalizing an arbitrary language name is {@code souther.compiler.CanonicalNames}'s job
 * instead, for exactly that reason: it needs {@code souther-runtime}'s {@code Normalization.nfc},
 * which this registry does not, and {@code souther-fmt} reads {@link #MODULES} without depending
 * on the compiler.
 */
public final class Reserved {

    private Reserved() {}

    /** One standard-library module: the namespace it is declared under and the qualifier a caller
     *  writes it as. {@code souther.list} is written {@code List}. */
    public record StdlibModule(String moduleName, String qualifier) {}

    /**
     * The standard library's modules, in the order the language names them. Everything that has to
     * put library modules in an order reads this one: which resources the loader reads and in
     * what order, which qualifiers exist, and the order a diagnostic offers candidates in when a
     * bare name could be several. Written here rather than derived from a map's entries, because
     * the iteration order of {@code Map.ofEntries} is not something a reader may be shown.
     */
    public static final List<StdlibModule> MODULES = List.of(
            new StdlibModule("souther.bool", "Bool"),
            new StdlibModule("souther.string", "String"),
            new StdlibModule("souther.map", "Map"),
            new StdlibModule("souther.list", "List"),
            new StdlibModule("souther.set", "Set"),
            new StdlibModule("souther.date", "Date"),
            new StdlibModule("souther.time", "Time"),
            new StdlibModule("souther.datetime", "DateTime"),
            new StdlibModule("souther.instant", "Instant"),
            new StdlibModule("souther.int", "Int"),
            new StdlibModule("souther.decimal", "Decimal"),
            new StdlibModule("souther.rational", "Rational"),
            new StdlibModule("souther.option", "Option"));

    /** Every qualifier a call may carry (spec §stdlib), in {@link #MODULES} order. */
    public static final Set<String> QUALIFIERS = qualifiers();

    /**
     * The qualifiers, and the registry checked for being one at all while they are collected.
     *
     * <p>Both halves have to be unique, and for different reasons. Two entries writing one
     * qualifier would publish two modules' declarations under one name. Two entries naming one
     * module would load that source twice and publish its declarations under two qualifiers — which
     * nothing downstream would report, because everything downstream derives from this and would
     * derive the same mistake. A registry that is the single source of an answer is checked where
     * it is written or nowhere.
     */
    private static Set<String> qualifiers() {
        Set<String> qualifiers = new LinkedHashSet<>();
        Set<String> modules = new LinkedHashSet<>();
        for (StdlibModule module : MODULES) {
            if (!qualifiers.add(module.qualifier())) {
                throw new IllegalStateException(
                        "two standard-library modules are written `" + module.qualifier() + "`");
            }
            if (!modules.add(module.moduleName())) {
                throw new IllegalStateException(
                        "the standard-library module " + module.moduleName() + " is listed twice");
            }
        }
        return Collections.unmodifiableSet(qualifiers);
    }

    /** Whether {@code qualifier} names a standard-library namespace a call or an import may write:
     *  {@code List} / {@code String} / {@code Map} / … (spec §stdlib). Asked here rather than of the
     *  loaded library, because which qualifiers there are is settled by {@link #MODULES} and reading
     *  it off the library made a reader that only wanted the names load and resolve every one of the
     *  modules behind them. */
    public static boolean isQualifier(String qualifier) {
        return QUALIFIERS.contains(qualifier);
    }

    /** Whether {@code moduleName} is the reserved namespace or a module inside it. The core
     *  privileges — declaring an {@code intrinsic}, declaring a {@code private let} — are the ones
     *  this answers for. */
    public static boolean isNamespace(String moduleName) {
        return moduleName != null
                && (moduleName.equals("souther") || moduleName.startsWith("souther."));
    }
}
