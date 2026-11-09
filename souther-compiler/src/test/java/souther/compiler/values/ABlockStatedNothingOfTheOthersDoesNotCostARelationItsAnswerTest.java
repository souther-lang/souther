package souther.compiler.values;

import org.junit.jupiter.api.Test;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * What a relation shows of the blocks it is about is shown still when pairs are added that name
 * none of them. The bounds on what is narrowed, counted and looked through are for the part of the
 * relation a lack is about, so blocks no pair joins to it cannot make it too large.
 */
class ABlockStatedNothingOfTheOthersDoesNotCostARelationItsAnswerTest {

    private static Apartness<String> triangleBesideAPathOf(int blocks) {
        Apartness<String> out = Apartness.of("p", "q")
                .and(Apartness.of("q", "r")).and(Apartness.of("p", "r"));
        for (int i = 0; i < blocks - 1; i++) {
            out = out.and(Apartness.of("f" + i, "f" + (i + 1)));
        }
        return out;
    }

    /** Three blocks each stated to differ from the others, over two values, and a path of blocks
     *  with three values each, which stands whatever its length. */
    private static Apartness.Reduction<String> reduced(Apartness<String> relation) {
        return relation.reduce((block, _) -> new Admits.These(
                block.members().iterator().next().startsWith("f")
                        ? Set.of(Value.text("x"), Value.text("y"), Value.text("z"))
                        : Set.of(Value.text("A"), Value.text("B"))));
    }

    @Test
    void aTriangleOverTwoValuesStillHoldsNothingBesideAPathOfAnyLength() {
        Apartness.Reduction<String> alone = reduced(triangleBesideAPathOf(3));
        assertInstanceOf(Apartness.Reduction.Nothing.class, alone);

        for (int blocks : new int[] {31, 64, 100}) {
            Apartness.Reduction<String> beside = reduced(triangleBesideAPathOf(blocks));

            assertInstanceOf(Apartness.Reduction.Nothing.class, beside,
                    "the triangle is refused beside a path of " + blocks + " blocks");
            assertEquals(((Apartness.Reduction.Nothing<String>) alone).lacks(),
                    ((Apartness.Reduction.Nothing<String>) beside).lacks(),
                    "and what it shows is what it shows alone");
        }
    }

    @Test
    void aRelationThatStandsStillStandsBesideAnotherThatDoes() {
        Apartness<String> relation = Apartness.of("p", "q");
        for (int i = 0; i < 40; i++) {
            relation = relation.and(Apartness.of("f" + i, "f" + (i + 1)));
        }

        assertInstanceOf(Apartness.Reduction.Standing.class, reduced(relation));
    }
}
