package souther.compiler.check;

import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashSet;
import java.util.Set;

/**
 * Which enumerations list a unit value among their cases, for a reader working out what orders it.
 *
 * <p>A relation and not a choice. A unit may be a case of no enumeration, of one, or of several
 * that place it differently, and what orders a value is read off all of them: one is the order,
 * several are none, and a union of cases is ordered by the enumerations every member is listed by.
 * Answered as the one it settles on, a union could no longer be told from a member that has none.
 *
 * <p>A fact about the declarations of the value's module and of nothing else, since a sum and its
 * cases are declared together. That module's sums are what answers it, so a reader asking it of
 * many values is asking one module question many times — which is why the answer is the
 * compilation's to hold, once for each module, and not a reader's to work out.
 */
@FunctionalInterface
public interface EnumerationListings {

    /** Every enumeration that lists {@code value}, and none where no enumeration does. */
    Set<TypeSymbol> of(TypeSymbol.AtModule value);

    /** Nothing declared anywhere — for a reading over primitives, which asks of no declaration. */
    EnumerationListings NONE = _ -> Set.of();

    /**
     * The same question read off the declarations in {@code symbols}, each time it is asked: every
     * sum of the value's module, each asked whether it is an enumeration and opened if it is.
     *
     * <p>For the walks that have not been handed the compilation's answer, and for the one that
     * makes what a declaration says: there the declaration being made is taken out of
     * {@code published}, and an answer held by the compilation would be read past that.
     */
    static EnumerationListings asWritten(Symbols symbols, DeclarationKinds kinds,
                                         PublishedDeclarations published) {
        return value -> {
            Set<TypeSymbol> owners = new LinkedHashSet<>();
            TypeOps.forEachEnumeration(value.module(), symbols.declaredNamesIn(value.module()),
                    kinds, published,
                    (enumeration, listed) -> {
                        if (listed.contains(value)) {
                            owners.add(enumeration);
                        }
                    });
            return owners;
        };
    }
}
