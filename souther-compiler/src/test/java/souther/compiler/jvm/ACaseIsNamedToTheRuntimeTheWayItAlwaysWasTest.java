package souther.compiler.jvm;

import souther.compiler.types.LanguageCaseId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a case is called between a generated class and souther-runtime, written out.
 *
 * <p>A characterization and not a preference. These pairs are in class files this compiler has
 * already written: a generated comparison holds the qualified form as a constant, and a
 * {@code DeclaredCase} is built from the two parts. A jar compiled before this change is read by a
 * runtime that compares against what it was given, so a spelling that moved here would be a jar
 * whose answers stopped matching.
 *
 * <p>Which is the whole reason the namespaces live in the ABI rather than in the compiler's model of
 * an identity. {@code souther} and {@code souther.runtime} are what this protocol has always said,
 * and there is no module of either name; the model says what declared a thing, and this says what
 * the protocol calls it. The two are allowed to differ and here they do.
 *
 * <p>Both closed sets are read rather than a few written out, so a case added to either is given a
 * token here or fails.
 */
class ACaseIsNamedToTheRuntimeTheWayItAlwaysWasTest {

    @Test
    void aDeclarationOfAModuleIsNamedByThatModule() {
        TypeSymbol denied = TypeSymbols.declared(new TypeKey("foo.bar", "Denied"));

        assertEquals(new RuntimeCaseToken("foo.bar", "Denied"), SoutherJvmAbi.caseTokenOf(denied));
        assertEquals("foo.bar.Denied", SoutherJvmAbi.caseTokenOf(denied).qualified());
    }

    @Test
    void everyPrimitiveKeepsTheNamespaceItWasCompiledUnder() {
        Map<String, String> tokens = new LinkedHashMap<>();
        for (Type.Prim prim : Type.Prim.values()) {
            tokens.put(prim.name(), SoutherJvmAbi.caseTokenOf(TypeSymbol.primitive(prim)).qualified());
        }

        assertEquals(Map.of(
                        "INT", "souther.Int",
                        "STRING", "souther.String",
                        "BOOL", "souther.Bool",
                        "DECIMAL", "souther.Decimal",
                        "DATE", "souther.Date",
                        "TIME", "souther.Time",
                        "DATETIME", "souther.DateTime",
                        "INSTANT", "souther.Instant",
                        "RAW", "souther.Raw"),
                tokens);
    }

    @Test
    void everyCaseTheLanguageGivesKeepsTheNamespaceItWasCompiledUnder() {
        Map<String, String> tokens = new LinkedHashMap<>();
        for (LanguageCaseId id : LanguageCaseId.values()) {
            tokens.put(id.name(),
                    SoutherJvmAbi.caseTokenOf(new TypeSymbol.LanguageCase(id)).qualified());
        }

        assertEquals(Map.of(
                        // Beside the primitives, which is where they were filed.
                        "SOME", "souther.Some",
                        "NONE", "souther.None",
                        // Under the package souther-runtime ships their classes in, which is what
                        // the pair said when the namespace and the package were one string.
                        "DIVISION_BY_ZERO", "souther.runtime.DivisionByZero",
                        "NOT_A_NUMBER", "souther.runtime.NotANumber",
                        "NOT_A_DATE", "souther.runtime.NotADate",
                        "NOT_A_TIME", "souther.runtime.NotATime"),
                tokens);
    }
}
