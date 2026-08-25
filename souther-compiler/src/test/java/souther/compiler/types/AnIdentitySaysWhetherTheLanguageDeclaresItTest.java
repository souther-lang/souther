package souther.compiler.types;

import org.junit.jupiter.api.Test;

import souther.compiler.Reserved;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a module of some compilation declared something, or the language did, is a question the
 * identity answers.
 *
 * <p>A reader that works it out from the module name is a reader that has to know the namespace
 * rule, and every one that did knew a different half of it: {@code isPrimitive()} for {@code
 * souther}, a comparison against {@code TypeSymbol.RUNTIME} for {@code souther.runtime}, and in one
 * place a test against the standard library's qualifiers, which are not module names at all
 * (#1049). One question, asked of the thing that has the answer.
 *
 * <p>Off the address and not off how the identity was minted. {@link TypeSymbols} has two ways in —
 * {@code declared} and {@code ofLanguage} — and which one a given identity came through is not a
 * fact about the declaration: {@code Declarations.identify} answers for the language's own
 * vocabulary through {@code declared}, so an origin kept from the factory would make one address two
 * different things by route. Held here as: equal identities answer alike.
 */
class AnIdentitySaysWhetherTheLanguageDeclaresItTest {

    @Test
    void aPrimitiveCaseNameIsDeclaredByTheLanguage() {
        assertTrue(TypeSymbol.primitive("Int").isDeclaredByLanguage());
    }

    @Test
    void soAreOptionsTwoCases() {
        assertTrue(TypeSymbol.SOME.isDeclaredByLanguage());
        assertTrue(TypeSymbol.NONE.isDeclaredByLanguage());
    }

    /** The other half of the namespace, which {@code isPrimitive()} does not answer for. */
    @Test
    void soIsABuiltInErrorCase() {
        TypeSymbol error = new TypeSymbol.LanguageCase(LanguageCaseId.DIVISION_BY_ZERO);

        assertTrue(error.isDeclaredByLanguage());
        assertFalse(error.isPrimitive(), "which is not the same question");
    }

    /** And so is what the standard library declares, which is a module's declaration and no
     *  compilation's: {@code souther.decimal} writes {@code RoundingMode} and nothing here does. */
    @Test
    void soIsWhatTheStandardLibraryDeclares() {
        assertTrue(TypeSymbols.declared(new TypeKey("souther.decimal", "RoundingMode"))
                .isDeclaredByLanguage());
        assertFalse(TypeSymbols.declared(new TypeKey("demo", "Quote")).isDeclaredByLanguage());
    }

    @Test
    void aTypeAModuleDeclaresIsNot() {
        assertFalse(TypeSymbols.declared(new TypeKey("probe.uni", "Amount"))
                .isDeclaredByLanguage());
    }

    /** A module may not take a reserved name, so nothing a compilation declares can answer yes by
     *  being spelled like one. */
    @Test
    void norIsATypeOfAModuleWhoseNameMerelyStartsWithTheSameWord() {
        assertFalse(TypeSymbols.declared(new TypeKey("southerly.billing", "Amount"))
                .isDeclaredByLanguage());
    }

    @Test
    void aHelperAndABehaviorAnswerTheSameWay() {
        assertFalse(new ValueName.Helper("probe.uni", "ok").isDeclaredByLanguage());
        assertFalse(new ValueName.Behavior("probe.uni", "half").isDeclaredByLanguage());
        assertTrue(new ValueName.Helper("souther.option", "withDefault").isDeclaredByLanguage());
    }

    /**
     * How the question was got wrong: two identities equal to each other answering differently is
     * what a provenance kept from the factory would have allowed.
     *
     * <p>There is one way to an address's identity now, so the two sides of this are the same
     * expression written twice. It is left standing because what it holds is that they are: an
     * identity is its address and carries nothing about how it was reached.
     */
    @Test
    void twoIdentitiesOfOneAddressAnswerAlike() {
        TypeKey address = new TypeKey("souther.decimal", "RoundingMode");
        TypeSymbol minted = TypeSymbols.declared(address);
        TypeSymbol identified = TypeSymbols.declared(address);

        assertEquals(minted, identified);
        assertEquals(minted.isDeclaredByLanguage(), identified.isDeclaredByLanguage());
    }

    /**
     * A standard-library qualifier is not a module name, and no module name is a qualifier.
     *
     * <p>The two are different vocabularies: a qualifier is what a call writes ({@code Option}), and
     * a module name is what resolution settled ({@code souther.option}). Holding a resolved module
     * against {@link Reserved#isQualifier} is a test nothing can pass, which is why the crossing's
     * exclusion of the standard library never fired and a {@code match} on an optional went looking
     * for a {@code souther} artifact.
     */
    @Test
    void aQualifierIsNeverTheModuleOfAnIdentity() {
        List<String> qualifiersThatAreModuleNames = new ArrayList<>();
        List<String> moduleNamesOutsideTheNamespace = new ArrayList<>();
        for (Reserved.StdlibModule each : Reserved.MODULES) {
            assertTrue(Reserved.isQualifier(each.qualifier()), each::qualifier);
            if (Reserved.isQualifier(each.moduleName())) {
                qualifiersThatAreModuleNames.add(each.moduleName());
            }
            if (!Reserved.isNamespace(each.moduleName())) {
                moduleNamesOutsideTheNamespace.add(each.moduleName());
            }
        }

        assertEquals(List.of(), qualifiersThatAreModuleNames,
                "a qualifier is the spelling a call writes, and never a module a name resolves to");
        assertEquals(List.of(), moduleNamesOutsideTheNamespace,
                "and every library module is inside the namespace, which is what answers for it");
        assertFalse(Reserved.isQualifier("souther"),
                "nor is the module the language's own vocabulary is addressed under");
    }
}
