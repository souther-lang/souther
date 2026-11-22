package souther.compiler.inputs;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.time.Duration;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

/**
 * Two readings that took the same values one after another are found equal in work that grows
 * with how many they took, and not by doubling at each.
 *
 * <p>What a node is taken as is a value read where the takings before it stood, so each taking
 * holds the chain before it twice: as what is older, and inside where its value is read. Two
 * copies of one chain compared part by part compare the pair of chains before each taking twice
 * over, and forty takings would be a million million comparisons.
 */
class TwoEqualChainsOfTakingsAreComparedInTheirLengthTest {

    private static final String MODEL = """
            module w1

            behavior f : (n: Int) -> Int
            let f (n) = if n < 3 then n else 3
            """;

    private static final int TAKINGS = 40;

    private static InputReads afterTakings(InputReads from, Core node) {
        InputReads at = from;
        for (int i = 0; i < TAKINGS; i++) {
            at = at.taking(node, new Denotation(node, at), 1);
        }
        return at;
    }

    @Test
    void fortyTakingsCompareAtOnce() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        ACompiledModel.compiles(compilation);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("w1")).value();
        RuleReadingSource rules = RuleReadings.of(compilation, "w1");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("w1")).value().get("f");
        InputReads reads = InputReads.ofParameters(inputs.parameterReads(),
                inputs.declared(rules), checked.elementBindings().get("f"),
                ValueDefinitions.of(checked.analysisBodies().get("f"), rules.newtypes()),
                inputs.dependencies());
        Core body = checked.behaviorBodies().get("f");

        InputReads one = afterTakings(reads, body);
        InputReads another = afterTakings(reads, body);

        assertNotSame(one, another);
        assertTimeoutPreemptively(Duration.ofSeconds(20), () -> {
            assertEquals(one, another);
            // The other way round, and against a third: what one comparison kept is of that pair
            // and that way, and the next costs its length again and no more.
            assertEquals(another, one);
            InputReads third = afterTakings(reads, body);
            assertEquals(third, one);
            assertEquals(one, third);
        });
    }
}
