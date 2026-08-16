package souther.compiler.check;

import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.Front;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * The one way an {@code import List ( ... )} line fails as a library import comes back as a
 * refusal, and it is raised nowhere.
 *
 * <p>The contract this rests on, as against what a reader does with it. It used to be raised, so a
 * reader could only tell it apart by catching and taking a diagnostic apart, and a reader that did
 * not catch lost the compile. What it says, and where, is the reader's: a line of a source this
 * compilation has is quoted on that line, and the same failure in a module read off the class path
 * is a fact about an artifact.
 *
 * <p>One way, where there used to be three. A name two lines both bring in, and a name this module
 * also declares, are not failures of a library import — they are contests between what the lines
 * claim, and are settled where every claim is ({@link Scoping}). Settled here instead, what an
 * author was told depended on whether the name happened to arrive from the library: the same two
 * lines naming a user module were answered by a different rule, and one crossing the two was
 * answered by neither.
 *
 * <p>What is left is a fact about the library rather than about this module — it publishes no
 * operation of that name — so the line claims nothing, and there is nothing for a contest to be
 * between.
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

    /** A contest between claims, which this does not settle and does not see. */
    @Test
    void aNameTwoLinesBothBringInIsNoFailureOfEitherLine() {
        assertEquals(List.of(), refusedIn("""
                module app.own
                import Map ( insert )
                import Set ( insert )
                """));
    }

    /** The same, for a claim against a declaration written here. */
    @Test
    void aNameThisModuleAlsoDeclaresIsNoFailureOfTheLine() {
        assertEquals(List.of(), refusedIn("""
                module app.own
                import List ( map )

                let map (x) = x
                """));
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
