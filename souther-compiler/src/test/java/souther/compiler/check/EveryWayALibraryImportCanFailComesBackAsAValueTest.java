package souther.compiler.check;

import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.Front;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * Every way an {@code import List ( ... )} line can fail comes back as a refusal, and which of them
 * it was is on the value.
 *
 * <p>The contract this rests on, as against what a reader does with it. Two of the three used to be
 * raised, so a reader could only tell them apart by catching and taking a diagnostic apart, and a
 * reader that caught neither lost the compile. What each of them says, and where, is the reader's:
 * a line of a source this compilation has is quoted on that line, and the same failure in a module
 * read off the class path is a fact about an artifact.
 */
class EveryWayALibraryImportCanFailComesBackAsAValueTest {

    /** What the check refused in {@code source}, which declares {@code app.own}. */
    private static List<Exposing.Refusal> refusedIn(String source) {
        Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
        Exposing.Checked checked = compilation.db().ask(new Front.Checked("app.own")).value();
        return checked.refused();
    }

    @Test
    void aNameTheLibraryDoesNotHave() {
        List<Exposing.Refusal> refused = refusedIn("""
                module app.own
                import List ( noSuchOperation )
                """);

        assertEquals(1, refused.size(), refused::toString);
        Exposing.Refusal.NoSuchLibraryFunction said = assertInstanceOf(
                Exposing.Refusal.NoSuchLibraryFunction.class, refused.get(0));
        assertEquals("noSuchOperation", said.name());
        assertEquals("List", said.imp().module(), "the line it was written on says which module");
    }

    @Test
    void oneNameFromTwoLibraryModules() {
        List<Exposing.Refusal> refused = refusedIn("""
                module app.own
                import Map ( insert )
                import Set ( insert )
                """);

        assertEquals(1, refused.size(), refused::toString);
        Exposing.Refusal.BroughtTwice said = assertInstanceOf(
                Exposing.Refusal.BroughtTwice.class, refused.get(0));
        assertEquals("insert", said.name());
        assertEquals("Map.insert", said.earlier().qualified(), "the one that has it");
        assertEquals("Set.insert", said.andThis().qualified(), "the one that does not get it");
    }

    @Test
    void aNameThisModuleAlsoDeclares() {
        List<Exposing.Refusal> refused = refusedIn("""
                module app.own
                import List ( map )

                let map (x) = x
                """);

        assertEquals(1, refused.size(), refused::toString);
        Exposing.Refusal.CollidesWithADeclaration said = assertInstanceOf(
                Exposing.Refusal.CollidesWithADeclaration.class, refused.get(0));
        assertEquals("map", said.name());
    }

    /**
     * Two lines that each fail are two refusals, and the first does not stand for the second.
     *
     * <p>What raising cost. The check stopped at whichever line it reached first, so an author with
     * two mistaken imports fixed one and was told about the next — and a module off the class path
     * with two of them was as unreadable for the first as for both.
     */
    @Test
    void twoFailingLinesAreTwoRefusals() {
        List<Exposing.Refusal> refused = refusedIn("""
                module app.own
                import List ( noSuchOperation )
                import Map ( alsoNotThere )
                """);

        assertEquals(2, refused.size(), refused::toString);
        assertEquals(List.of("noSuchOperation", "alsoNotThere"),
                refused.stream().map(Exposing.Refusal::name).toList(),
                "in the order the lines are written");
    }
}
