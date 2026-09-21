package souther.compiler.core;

import souther.compiler.types.LanguageCaseId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What a kernel can answer with is read off the result it declared.
 *
 * <p>The members of the declared union are where the cases are, and a reader wanting one wants the
 * member itself: a typed identity it can hand to whatever represents it, rather than a spelling to
 * look up. Held here of unions written on purpose, because what any one kernel of the library
 * declares is the library's answer and would say nothing about a result this projection has not
 * been given.
 */
class AKernelsResultNamesTheCasesItCanAnswerWithTest {

    private static final TypeSymbol INT = TypeSymbol.primitive(Type.Prim.INT);

    private static final TypeSymbol.LanguageCase DIVISION_BY_ZERO =
            new TypeSymbol.LanguageCase(LanguageCaseId.DIVISION_BY_ZERO);

    private static final TypeSymbol.LanguageCase NOT_WHOLE =
            new TypeSymbol.LanguageCase(LanguageCaseId.NOT_WHOLE);

    @Test
    void aResultThatIsAValueAndACaseNamesTheCase() {
        assertEquals(Set.of(DIVISION_BY_ZERO),
                answering(union(INT, DIVISION_BY_ZERO)).languageCaseMembers());
    }

    /**
     * And one naming two cases names both.
     *
     * <p>The reason this is a set and not an option. A projection answering the one case there
     * happens to be today would be a contract saying there is at most one, and what would be
     * refused the day a kernel declares two is the language rather than the output that cannot
     * lower them.
     */
    @Test
    void andOneThatNamesTwoNamesBoth() {
        assertEquals(Set.of(DIVISION_BY_ZERO, NOT_WHOLE),
                answering(union(INT, DIVISION_BY_ZERO, NOT_WHOLE)).languageCaseMembers());
    }

    /** A kernel that cannot depart names none. */
    @Test
    void aResultThatIsAValueNamesNone() {
        assertEquals(Set.of(), answering(Type.INT).languageCaseMembers());
    }

    /** A result that is a case and nothing else names it: the members of a declared result are what
     *  this reads, and a result of one member is a result all the same. */
    @Test
    void aResultThatIsACaseNamesIt() {
        assertEquals(Set.of(DIVISION_BY_ZERO),
                answering(new Type.Ref(DIVISION_BY_ZERO)).languageCaseMembers());
    }

    /**
     * A declared {@code Option} names none.
     *
     * <p>{@code Some} and {@code None} are cases of the language, but a declared result never holds
     * them as union members to be excluded: {@code Option<T>} is {@link Type.OptionOf}, not a union
     * of the two, and a written {@code Some} or {@code None} outside a match arm resolves to neither
     * — name resolution answers that question before a result reaches here at all.
     */
    @Test
    void aDeclaredOptionNamesNone() {
        assertEquals(Set.of(), answering(Type.option(Type.INT)).languageCaseMembers());
    }

    /**
     * Membership, and not the order the members come back in.
     *
     * <p>Two writings of one union are one value, so there is no order here for an output to take
     * for a calling convention. Asked by writing the same union both ways round and comparing what
     * comes back as the set it is.
     */
    @Test
    void andTheAnswerIsMembershipRatherThanAnOrder() {
        assertEquals(answering(union(INT, DIVISION_BY_ZERO, NOT_WHOLE)).languageCaseMembers(),
                answering(union(NOT_WHOLE, DIVISION_BY_ZERO, INT)).languageCaseMembers());
    }

    /** And a reader of the projection does not get to write to it. */
    @Test
    void andAReaderCannotWriteToWhatItWasHanded() {
        Set<TypeSymbol.LanguageCase> named =
                answering(union(INT, DIVISION_BY_ZERO)).languageCaseMembers();

        assertThrows(UnsupportedOperationException.class, () -> named.add(NOT_WHOLE));
    }

    private static KernelSignature answering(Type result) {
        return new KernelSignature(List.of(), result);
    }

    private static Type union(TypeSymbol... members) {
        return new Type.Union(new LinkedHashSet<>(List.of(members)));
    }
}
