package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.diag.CompileException;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/** The surface and well-formedness rules of a behavior's postcondition. */
class EnsuresDeclarationTest {

    private static final String SINGLE = """
            module example.one

            data Id = Int

            behavior echo : (id: Id) -> Id
                ensures same = value == id

            let echo (id) = id
            """;

    private static final String SUM = """
            module example.sum

            data Id = Int
            data Found = { id: Id }
            data Missing = { id: Id }
            data Other = { id: Id }

            behavior lookup : (id: Id) -> Found | Missing
                ensures Found | Missing -> value.id == id
            """;

    @Test
    void bothSurfaceFormsCompile() {
        assertDoesNotThrow(() -> Compiler.compile(SINGLE));
        assertDoesNotThrow(() -> Compiler.compile(SUM));
    }

    @Test void aClauseNamesTheAnswer() {
        refused(SINGLE.replace("value == id", "id == id"), "E1616");
    }

    @Test void aClauseNamesAParameter() {
        refused(SINGLE.replace("value == id", "value == value"), "E1617");
    }

    @Test void valueIsReservedForTheAnswer() {
        refused(SINGLE.replace("id: Id", "value: Id")
                .replace("(id) = id", "(value) = value"), "E1618");
    }

    @Test void aNamedArmIsAnOutputCase() {
        refused(SUM.replace("Found | Missing ->", "Other ->"), "E1619");
    }

    @Test void aSumClauseNamesArms() {
        refused(SUM.replace("Found | Missing -> ", ""), "E1620");
    }

    @Test void aSingleOutputClauseNamesNoArm() {
        refused(SINGLE.replace("value == id", "Id -> value == id"), "E1621");
    }

    @Test void clauseNamesAreDistinct() {
        refused(SINGLE.replace("let echo", "    ensures same = value == id\n\nlet echo"),
                "E1622");
    }

    @Test void underscoreIsNotAClauseName() {
        refused(SINGLE.replace("same =", "_ ="), "E1623");
    }

    @Test void aCompositionCarriesNoClause() {
        refused("""
                module example.pipe
                behavior one : (id: Int) -> Int
                behavior two : (id: Int) -> Int
                behavior both = one >-> two
                    ensures value == id
                """, "E1624");
    }

    private static void refused(String source, String code) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(source));
        assertEquals(code, e.code());
    }
}
