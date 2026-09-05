package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.SequencedMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A walk handed a numbering is held to having realized it.
 *
 * <p>What a numbering means is decided once, by whoever holds the bodies, and a later walk of them
 * takes that numbering rather than deciding a second one. So the addresses two walks hand out are
 * addresses of one numbering — which is what a reader comparing an arm of one with an arm of the
 * other is asking about, and it is now the same question rather than one answered again per pair.
 *
 * <p><b>Which is why the walk is checked and not trusted.</b> Deciding the numbering twice, a walk
 * that came to number a place differently made a second numbering, and the two were unequal
 * wherever they met. Taking one that was decided elsewhere, such a walk hands out an address
 * carrying a numbering that says the number means something else — and nothing downstream can see
 * the difference, because the address it is compared with says the same. So the disagreement is
 * refused here, where the walk and the numbering are both in hand.
 */
class AWalkRealizesTheNumberingItWasGivenTest {

    private static final String MODEL = """
            module demo

            behavior over : (a: Int, b: Int) -> Int
            let over (a, b) = if a >= b then a else b

            behavior graded : (n: Int) -> Int
            let graded (n) = if n >= 1 then 1 else 2
            """;

    /** The same two behaviors, declared the other way round: the same bodies, numbered from the
     *  other end. */
    private static final String DECLARED_THE_OTHER_WAY = """
            module demo

            behavior graded : (n: Int) -> Int
            let graded (n) = if n >= 1 then 1 else 2

            behavior over : (a: Int, b: Int) -> Int
            let over (a, b) = if a >= b then a else b
            """;

    /** The same bodies under another name. */
    private static final String ANOTHER_MODULE = MODEL.replace("module demo", "module other");

    /** One behavior answering something else, so the bodies do different things. */
    private static final String ANOTHER_BODY = MODEL.replace("then 1 else 2", "then 3 else 2");

    @Test
    void aWalkOfTheBodiesItWasIssuedOverHandsOutAddressesOfIt() {
        Bodies.Elaborated checked = checked(MODEL);
        NumberingIdentity issued = checked.numberingIdentity();

        CoverageSites.Plan plan = CoverageSites.under(bodiesOf(checked), checked.decisions(),
                checked.supplied(), issued);

        assertSame(issued, plan.identity(),
                "the walk realizes the numbering it was given rather than deciding one");
        assertTrue(!plan.sites().isEmpty(), "the model under test has places to number");
        for (CoverageSites.Site site : plan.sites()) {
            assertSame(issued, site.index().numbering(),
                    () -> "every address this walk hands out is an address of that numbering: "
                            + site.index());
        }
    }

    /** And a walk that numbered other places is refused, saying which number went elsewhere. */
    @Test
    void aWalkThatNumberedOtherPlacesIsRefused() {
        Bodies.Elaborated checked = checked(MODEL);
        Bodies.Elaborated theOtherWay = checked(DECLARED_THE_OTHER_WAY);

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> CoverageSites.under(bodiesOf(theOtherWay), theOtherWay.decisions(),
                        theOtherWay.supplied(), checked.numberingIdentity()));

        assertEquals(checked.numberingIdentity().executable(),
                theOtherWay.numberingIdentity().executable(),
                "the bodies do the same things, so what is left is where the numbers went");
        assertTrue(refused.getMessage().contains("handed 0 out for"),
                () -> "the refusal says which number went to another place: "
                        + refused.getMessage());
    }

    /** And a walk of bodies that do something else is refused, saying which behavior. */
    @Test
    void aWalkOfBodiesThatDoSomethingElseIsRefused() {
        Bodies.Elaborated checked = checked(MODEL);
        Bodies.Elaborated other = checked(ANOTHER_BODY);

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> CoverageSites.under(bodiesOf(other), other.decisions(), other.supplied(),
                        checked.numberingIdentity()));

        assertTrue(refused.getMessage().contains("`graded`"),
                () -> "the refusal says whose body it is: " + refused.getMessage());
    }

    /** And a walk of another module's bodies is refused, whatever they hold. */
    @Test
    void aWalkOfAnotherModulesBodiesIsRefused() {
        Bodies.Elaborated checked = checked(MODEL);
        Bodies.Elaborated elsewhere = checked(ANOTHER_MODULE);

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> CoverageSites.under(bodiesOf(elsewhere), elsewhere.decisions(),
                        elsewhere.supplied(), checked.numberingIdentity()));

        assertTrue(refused.getMessage().contains("issued for demo")
                        && refused.getMessage().contains("walk of other"),
                () -> "the refusal says whose module each is: " + refused.getMessage());
    }

    private static souther.compiler.coverage.ModuleBodies bodiesOf(Bodies.Elaborated checked) {
        SequencedMap<String, Core> bodies = new LinkedHashMap<>(checked.behaviorBodies());
        return new ModuleBodies(checked.module(), bodies);
    }

    private static Bodies.Elaborated checked(String source) {
        Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked =
                compilation.db().ask(new Bodies.Checked(module)).value();
        assertTrue(checked != null,
                () -> "the model under test compiled to nothing: " + compilation.errors());
        return checked;
    }
}
