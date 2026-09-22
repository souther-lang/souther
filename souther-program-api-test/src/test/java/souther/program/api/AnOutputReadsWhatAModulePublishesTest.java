package souther.program.api;

import souther.compiler.diag.CompileException;
import souther.compiler.program.CheckedBehavior;
import souther.compiler.program.CheckedData;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.program.Publication;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What a module publishes, as an output reads it.
 *
 * <p>What a module publishes is its {@code exposing} clause and nothing else, and an output that
 * has to know it — to decide what its artifact says about a name, among other things — reads it
 * here. What an artifact then makes visible is a second question and not this one: a published
 * helper runs in the module that reads it and is emitted on a class that module keeps, and an
 * injected behavior's base is public whatever the clause says. An output working the first out for
 * itself would publish a surface the module never stated, and the only other route is reading the
 * source again, which is
 * the re-derivation this boundary exists to stop.
 */
class AnOutputReadsWhatAModulePublishesTest {

    private static final String WITH_A_CLAUSE = """
            module pricing exposing ( total )

            behavior total : (a: Int) -> Int
            let total (a) = kept(a)

            behavior kept : (a: Int) -> Int
            let kept (a) = a + 1
            """;

    /**
     * A module that writes no clause publishes nothing, which is what an importer is told: naming
     * one of these in an import is E1507. An empty clause says the same thing, and the language
     * makes no distinction between the two.
     */
    private static final String WITH_NONE = """
            module plainly

            behavior one : (a: Int) -> Int
            let one (a) = a

            behavior other : (a: Int) -> Int
            let other (a) = a
            """;

    private static final String WITH_AN_EMPTY_CLAUSE = """
            module emptily exposing ()

            behavior one : (a: Int) -> Int
            let one (a) = a
            """;

    private static final String WITH_A_DATA_CLAUSE = """
            module amounts exposing ( Amount )

            data Amount = { value: Int }
            data Kept = { value: Int }
            """;

    private static final String WITH_ANOTHER_DATA = """
            module elsewhere

            data Amount = { value: Int }
            """;

    @Test
    void aNameTheClauseListsIsPublishedAndOneItDoesNotIsKept() {
        CheckedModule module = CheckedProgram.of(List.of(WITH_A_CLAUSE)).module("pricing");

        assertEquals(Publication.PUBLISHED, publicationOf(module, "total"));
        assertEquals(Publication.KEPT, publicationOf(module, "kept"));
    }

    @Test
    void aModuleThatWritesNoClausePublishesNothing() {
        CheckedModule module = CheckedProgram.of(List.of(WITH_NONE)).module("plainly");

        assertEquals(Publication.KEPT, publicationOf(module, "one"));
        assertEquals(Publication.KEPT, publicationOf(module, "other"));
    }

    /** And an empty clause is that same answer and not another one. */
    @Test
    void anEmptyClausePublishesNothingEither() {
        CheckedModule module = CheckedProgram.of(List.of(WITH_AN_EMPTY_CLAUSE)).module("emptily");

        assertEquals(Publication.KEPT, publicationOf(module, "one"));
    }

    /** A name this module does not declare is not a name it keeps, and is refused rather than answered. */
    @Test
    void aBehaviorThisModuleDoesNotDeclareIsRefusedRatherThanKept() {
        CheckedModule module = CheckedProgram.of(List.of(WITH_A_CLAUSE)).module("pricing");

        assertThrows(IllegalArgumentException.class, () -> module.publicationOf(
                new ValueName.Behavior("pricing", "nobodyWroteThis")));
        assertThrows(IllegalArgumentException.class, () -> module.publicationOf(
                new ValueName.Behavior("somewhere.else", "total")));
    }

    /**
     * What that answer means, asked of the language rather than taken from this reading of it: a
     * name kept is one an importer may not name, and the refusal is where the two meet.
     */
    @Test
    void whatIsKeptIsWhatAnImporterIsRefused() {
        assertThrows(CompileException.class, () -> CheckedProgram.of(List.of(WITH_NONE, """
                module reader
                import plainly ( one )

                behavior used : (a: Int) -> Int
                let used (a) = one(a)
                """)));
    }

    /** A data answers the same way a behavior does: named by the clause, published; otherwise kept. */
    @Test
    void aDataTheClauseListsIsPublishedAndOneItDoesNotIsKept() {
        CheckedModule module = CheckedProgram.of(List.of(WITH_A_DATA_CLAUSE)).module("amounts");

        assertEquals(Publication.PUBLISHED, publicationOfData(module, "Amount"));
        assertEquals(Publication.KEPT, publicationOfData(module, "Kept"));
    }

    /** A data another module declares is not this module's to answer for, and is refused. */
    @Test
    void aDataThisModuleDoesNotDeclareIsRefusedRatherThanKept() {
        CheckedProgram program = CheckedProgram.of(List.of(WITH_A_DATA_CLAUSE, WITH_ANOTHER_DATA));
        CheckedModule amounts = program.module("amounts");
        TypeSymbol.AtModule elsewheresAmount = dataNamed(program.module("elsewhere"), "Amount");

        assertThrows(IllegalArgumentException.class, () -> amounts.publicationOf(elsewheresAmount));
    }

    private static Publication publicationOf(CheckedModule module, String name) {
        for (CheckedBehavior behavior : module.behaviors()) {
            if (behavior.name().name().equals(name)) {
                return module.publicationOf(behavior.name());
            }
        }
        throw new AssertionError(module.name() + " declares no behavior " + name);
    }

    private static Publication publicationOfData(CheckedModule module, String name) {
        return module.publicationOf(dataNamed(module, name));
    }

    private static TypeSymbol.AtModule dataNamed(CheckedModule module, String name) {
        for (CheckedData declaration : module.data()) {
            if (declaration.name().name().equals(name)) {
                return declaration.name();
            }
        }
        throw new AssertionError(module.name() + " declares no data " + name);
    }
}
