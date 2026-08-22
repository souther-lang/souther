package souther.compiler.query;

import souther.compiler.types.TypeSymbol;

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

    private Evidence() {}
}
