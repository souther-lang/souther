package souther.compiler.partition;

import souther.compiler.check.Symbols;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.InputReads;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The comparisons one behavior's body writes, read where each of them stands.
 *
 * <p>The mechanical part of getting there and nothing else: compile the caller's module, find the
 * behavior, and walk it once. What a test claims about a comparison, and which declarations its
 * claim needs, stay the test's — a fixture shared between claims grows the declarations of each of
 * them, after which what a test compiles is no longer what it is about.
 *
 * <p>The source is asserted to compile here, because a model that does not is a test that measured
 * nothing and every claim below would be about an empty list.
 */
record ReadComparisons(List<ComparisonReadings.Reading> comparisons, Symbols symbols) {

    static ReadComparisons of(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(each -> each.diagnostic().code() + " "
                                + each.diagnostic().primary()).toList(),
                "the model under test compiles");
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        return new ReadComparisons(ComparisonReadings.of(
                checked.behaviorBodies().get(behavior),
                CoverageSites.of(checked.behaviorBodies(), checked.decisions(),
                        checked.supplied()),
                InputReads.of(compilation.db().ask(new Adequacy.Inputs(module)).value()
                        .get(behavior), checked.elementBindings().get(behavior)),
                symbols).all(), symbols);
    }

    /** The one comparison the body writes. A body writing two would leave a caller picking one of
     *  them by where it stands, after which a fixture could be about a rule nobody meant. */
    ComparisonReadings.Reading only() {
        assertEquals(1, comparisons.size(), () -> "the body under test writes one comparison: "
                + comparisons.stream().map(each -> each.comparison().pos().toString()).toList());
        return comparisons.get(0);
    }
}
