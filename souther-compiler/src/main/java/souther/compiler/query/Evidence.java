package souther.compiler.query;

import souther.compiler.types.TypeSymbol;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/** What {@link OutputCaseEvidence} and {@link InputCaseEvidence} share: how a set of cases is held.
 * The two are separate types because what their middle slot claims is different, and nothing should
 * be able to pass one for the other. */
final class Evidence {

    static Set<TypeSymbol> ordered(Set<TypeSymbol> of) {
        return of == null ? Set.of()
                : java.util.Collections.unmodifiableSet(new LinkedHashSet<>(of));
    }

    static List<TypeSymbol> missingFrom(Set<TypeSymbol> declared, Set<TypeSymbol> covered) {
        return declared.stream().filter(c -> !covered.contains(c)).toList();
    }

    /**
     * How many of {@code owed} are among {@code covered}, which is the numerator of a count out of
     * {@code owed}.
     *
     * <p>Never the size of {@code covered}. What the rows reached is a fact about the rows and can
     * hold a case the count is not out of — a case only an arm nothing reaches produces, one the
     * position's rules refuse — and its size over the size of {@code owed} would be a number about
     * two different sets.
     */
    static int amongThem(Collection<TypeSymbol> owed, Set<TypeSymbol> covered) {
        return (int) owed.stream().filter(covered::contains).count();
    }

    private Evidence() {}
}
