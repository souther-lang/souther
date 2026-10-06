package souther.compiler.partition;

import souther.compiler.Compiler;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.test.CheckedInObservation;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What the body of each fixture tells apart is what the fixture says it does.
 *
 * <p>Each fixture is one shape a body can have — a {@code match}, a comparison under another, a
 * decision no run reaches, one no subject could be named for — and why the answer is what it is is
 * said in the fixture, beside the model ({@link ToldApartCorpus}). This holds the compiler to every
 * one of them at once.
 *
 * <p>Every position and not only the one a fixture was written about. A position the fixture says
 * nothing about is one whose answer nobody checked, and a model edited to add one would leave it
 * so without anything failing.
 */
@CheckedInObservation
class EachFixtureIsToldApartAsItSaysTest {

    @Test
    void everyPositionOfEveryFixtureIsToldApartAsWritten() {
        List<ToldApartCorpus.Fixture> fixtures = ToldApartCorpus.all();
        List<String> differences = new ArrayList<>();
        for (ToldApartCorpus.Fixture fixture : fixtures) {
            Map<String, String> actual = toldApart(fixture);
            if (!actual.equals(fixture.expected())) {
                differences.add(fixture.file() + System.lineSeparator()
                        + "  written:  " + fixture.expected() + System.lineSeparator()
                        + "  answered: " + actual);
            }
        }
        assertEquals("", String.join(System.lineSeparator(), differences),
                () -> "of " + fixtures.size() + " fixtures, these were told apart otherwise than"
                        + " they say");
    }

    /** What the compiler says the body of {@code fixture}'s behavior tells apart, by position. */
    private static Map<String, String> toldApart(ToldApartCorpus.Fixture fixture) {
        Compilation compilation = Compiler.analyzedModules(List.of(fixture.source()),
                ModulePath.EMPTY, new ArrayList<>(), Adequacy.Asked.fullReport());
        Map<String, PartitionEvidence> byBehavior =
                compilation.db().ask(new Adequacy.Coverage(fixture.module())).value();
        if (byBehavior == null || byBehavior.get(ToldApartCorpus.BEHAVIOR) == null) {
            throw new AssertionError(fixture.file() + " has no measured `"
                    + ToldApartCorpus.BEHAVIOR + "`: " + compilation.texts());
        }
        Map<String, String> out = new LinkedHashMap<>();
        for (PartitionEvidence.AxisCoverage axis : byBehavior.get(ToldApartCorpus.BEHAVIOR).axes()) {
            out.put(axis.name(), ToldApartCorpus.spelled(axis.toldApart(), axis.classes().size()));
        }
        return out;
    }
}
