package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A plan answers for the nodes it was made from, and for no others however alike they are.
 *
 * <p>What an arm's number addresses is a place in a tree, and two compiles of one source produce
 * trees that are equal in every way a record compares. So a plan filed by value would answer for
 * either compile's nodes with the same confidence and be right about one of them. Filed by identity
 * it answers for the bodies it walked and returns nothing for anybody else's — and returning nothing
 * is what lets a caller emitting those other bodies find out, instead of writing a number that
 * addresses a place in a tree nobody is emitting.
 *
 * <p>Asked of the plan rather than of a generation. The generation is one caller of this, and what
 * it does with a lookup that came back empty is its own business; that the lookup comes back empty
 * is this.
 */
class APlanAddressesTheBodiesItWasMadeFromAndNotEqualOnesTest {

    private static final String MODULE = "example.trip";

    private static final String MODEL = """
            module example.trip

            data Submitted = { cost: Int }
            data Waiting = { cost: Int }

            behavior submit : (cost: Int) -> Submitted | Waiting
                constructs Submitted, Waiting

            let submit (cost) = {
                guard cost <= 100 else Waiting { cost = cost }
                Submitted { cost = cost }
            }
            """;

    /** The numbering of this module's bodies as one compile checked them. */
    private static CoverageSites.Plan planOfItsOwnCompile() {
        Compilation compilation = Compilation.ofSources(List.of(MODEL), ModulePath.EMPTY);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(MODULE)).value();
        assertNotNull(checked, "the model under test compiles");
        return checked.plan();
    }

    @Test
    void twoCompilesOfOneSourceNumberTreesThatCompareEqual() {
        Set<Core> here = new HashSet<>(planOfItsOwnCompile().byNode().keySet());
        Set<Core> there = new HashSet<>(planOfItsOwnCompile().byNode().keySet());

        assertTrue(here.size() > 0, "the model under test has arms to number");
        assertEquals(here, there,
                "the two compiles number trees that are equal, which is what makes the case below"
                        + " a question about identity and not about the program");
    }

    @Test
    void aPlanAnswersNothingForAnotherCompilesNodes() {
        CoverageSites.Plan here = planOfItsOwnCompile();
        CoverageSites.Plan there = planOfItsOwnCompile();

        for (Core node : there.byNode().keySet()) {
            assertNotNull(there.probesOf(node), "the plan answers for the nodes it was made from");
            assertNull(here.probesOf(node),
                    () -> "a plan of other bodies answered for " + node.getClass().getSimpleName()
                            + " at " + node.pos() + ", which is a place it never walked");
        }
    }
}
