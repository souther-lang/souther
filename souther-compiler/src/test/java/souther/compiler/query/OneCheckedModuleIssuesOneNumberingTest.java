package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.SiteNumbering;
import souther.compiler.meta.ModulePath;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A checked module issues its numbering once, and every reading of its bodies is of that one.
 *
 * <p>What a number a run was recorded at means is the check's answer, carried by the answer it
 * publishes. So the arms a claim names and the arms a measure counts are addresses of one
 * numbering, and asking whether two of them are the same place is asking about one number rather
 * than holding two accounts of what the module's numbers mean against each other.
 *
 * <p>Which is a fact about a checked module and not about a compilation: two checks of one module
 * decide two numberings that are equal, and what they are held together by is what
 * {@link souther.compiler.coverage.NumberingIdentity} says a numbering is.
 */
class OneCheckedModuleIssuesOneNumberingTest {

    private static final String MODEL = """
            module demo

            behavior over : (a: Int, b: Int) -> Int
            let over (a, b) = if a >= b then a else b
            """;

    /** A model whose body reads a name nothing declares, so the check answers with no bodies. */
    private static final String UNCHECKABLE = """
            module demo

            behavior over : (a: Int, b: Int) -> Int
            let over (a, b) = missing(a, b)
            """;

    /** Every plan derived from one checked module is of the numbering that module issued. */
    @Test
    void everyPlanOfOneCheckedModuleIsOfTheNumberingItIssued() {
        Compilation compilation = compiled(MODEL);
        Bodies.Elaborated checked = checkedOf(compilation);

        CoverageSites.Plan first = checked.plan();
        CoverageSites.Plan second = checked.plan();

        assertSame(checked.numberingIdentity(), first.identity(),
                "a plan of these bodies is of the numbering the check issued over them");
        assertSame(first.identity(), second.identity(),
                "so two readers hold one numbering, whether or not they hold one plan");
    }

    /** And so is the numbering a reader that wants no plan is given. */
    @Test
    void aReaderWantingOnlyTheNumberingIsGivenThatOne() {
        Compilation compilation = compiled(MODEL);
        Bodies.Elaborated checked = checkedOf(compilation);

        Optional<SiteNumbering> numbering =
                Adequacy.numberingOf(compilation.db(), checked.module());

        assertTrue(numbering.isPresent(), "the module was checked, so it has a numbering");
        assertSame(checked.numberingIdentity(), numbering.get().identity(),
                "read off the answer the check published rather than walked for again");
    }

    /**
     * And a module whose bodies were not checked has none.
     *
     * <p>Said against {@link CoverageSites.Plan#NONE}, which is what a reader wanting a plan is
     * given there and which carries a numbering of its own: a well formed numbering of the module
     * named by nothing, handing out no numbers. Nothing about it is malformed, so nothing refuses
     * it — and a reader told that was this module's numbering would align a recording against
     * places it was never near.
     */
    @Test
    void aModuleWhoseBodiesWereNotCheckedHasNoNumbering() {
        Compilation compilation = compiled(UNCHECKABLE);
        String module = compilation.modules().get(0);

        assertTrue(compilation.db().ask(new Bodies.Checked(module)).value() == null,
                "the model under test is one the check answers nothing for");
        assertEquals(Optional.empty(), Adequacy.numberingOf(compilation.db(), module),
                "no bodies were read, so there is nothing a number of them could mean");
        assertEquals("", CoverageSites.Plan.NONE.identity().module(),
                "and the empty plan's numbering is nobody's, not this module's");
    }

    private static Compilation compiled(String source) {
        Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
        compilation.answerEverything();
        return compilation;
    }

    private static Bodies.Elaborated checkedOf(Compilation compilation) {
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked =
                compilation.db().ask(new Bodies.Checked(module)).value();
        assertTrue(checked != null,
                () -> "the model under test compiled to nothing: " + compilation.errors());
        return checked;
    }
}
