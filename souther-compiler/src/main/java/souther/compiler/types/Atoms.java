package souther.compiler.types;

import java.util.List;

/**
 * What a value of a type can be, descending every case that is itself a sum.
 *
 * <p>A question this package cannot answer and {@link ResolvedCase} has to ask. What a type reaches
 * is a fact about the declarations a compile read, and nothing here holds one — so what is named
 * here is the asking, and the answering belongs to whoever read them.
 *
 * <p>Asked about the type a case stands over and about nothing else. The one caller passes
 * {@link CaseSelector#bound()}, so a case cannot come to cover the leaves of a type it does not
 * select: what crosses this is a type, and what comes back is what that type reaches.
 */
@FunctionalInterface
public interface Atoms {

    /** The atoms a value of {@code bound} can be, in first-reach declaration order. Empty where the
     *  type names no case at all. */
    List<TypeSymbol> of(Type bound);
}
