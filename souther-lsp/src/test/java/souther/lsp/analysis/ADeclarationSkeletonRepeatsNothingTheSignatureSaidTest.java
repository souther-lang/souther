package souther.lsp.analysis;

import souther.compiler.check.SpecImplementation.Parameter;
import souther.compiler.cst.TopLevelForm;
import souther.compiler.fmt.Skeleton;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a skeleton leaves for the author to write, and what it writes itself.
 *
 * <p>A hole is a place the compiler cannot settle. The name of an input is one: the implementation
 * may call it what it likes, and the behavior's own spelling is only a suggestion. The name of an
 * injected parameter is not — it names the behavior it injects, in the order they were declared, and
 * an implementation spelling it otherwise is refused — so it is written out. A skeleton that offered
 * it as a hole would be offering the author a choice the language does not give them, and the first
 * thing they did with it would be E1615.
 *
 * <p>The same rule settles the rest. An example row states as many arguments as the behavior takes
 * inputs, since what it depends on is supplied through {@code with} rather than passed, and it
 * writes a {@code with} for each dependency nothing already stands in for — a row that left one out
 * would be a row that cannot run, which is E1908.
 */
class ADeclarationSkeletonRepeatsNothingTheSignatureSaidTest {

    @Test
    void anInjectedParameterIsWrittenOutAndAnInputIsLeftToTheAuthor() {
        Skeleton.Built built = Skeleton.of(DeclarationSkeletons.implementing("place", List.of(
                new Parameter.Input("id"),
                new Parameter.Input("other"),
                new Parameter.Injected("findMember"))));
        assertEquals("let place (id, other, findMember) = body\n", built.text());
        assertEquals(List.of("id", "other", "body"), holeTextsOf(built));
    }

    /** A behavior that depends on nothing leaves every parameter to the author. */
    @Test
    void aBehaviorThatDependsOnNothingLeavesEveryParameterOpen() {
        Skeleton.Built built = Skeleton.of(DeclarationSkeletons.implementing("name",
                List.of(new Parameter.Input("id"), new Parameter.Input("fallback"))));
        assertEquals("let name (id, fallback) = body\n", built.text());
        assertEquals(List.of("id", "fallback", "body"), holeTextsOf(built));
    }

    /** A row takes the inputs and not what is injected, and says so with as many arguments. */
    @Test
    void aRowStatesAsManyArgumentsAsTheBehaviorTakesInputs() {
        Skeleton.Built built = Skeleton.of(DeclarationSkeletons.exampleFor("place", List.of(
                new Parameter.Input("id"),
                new Parameter.Input("other"),
                new Parameter.Injected("findMember")), List.of()));
        assertEquals("example place\n    | (id, other) -> expected\n", built.text());
        assertEquals(List.of("id", "other", "expected"), holeTextsOf(built));
    }

    /** And writes a {@code with} for each dependency nothing already stands in for. */
    @Test
    void aRowSuppliesWhatNothingElseStandsInFor() {
        Skeleton.Built built = Skeleton.of(DeclarationSkeletons.exampleFor("place",
                List.of(new Parameter.Input("id"), new Parameter.Injected("findMember")),
                List.of("findMember")));
        assertTrue(built.text().contains("with findMember = value"),
                "the row does not supply what nothing stands in for: " + built.text());
        assertEquals(List.of("id", "value", "expected"), holeTextsOf(built));
    }

    /**
     * A dependency something already stands in for is not asked for again.
     *
     * <p>A {@code with} written where a {@code fake} already answers is read first, so it would take
     * the table's place for that row alone. Offering one is offering to change what the row runs
     * against, which is not what completing a row is for.
     */
    @Test
    void aDependencySomethingAlreadyStandsInForIsNotAskedForAgain() {
        Skeleton.Built built = Skeleton.of(DeclarationSkeletons.exampleFor("place",
                List.of(new Parameter.Input("id"), new Parameter.Injected("findMember")),
                List.of()));
        assertTrue(!built.text().contains("with"),
                "a row was offered a stand-in for a dependency that has one: " + built.text());
    }

    /**
     * Every form has a skeleton, and every one of them is a declaration.
     *
     * <p>{@link Skeleton#of} refuses tokens that do not parse, so building each of these is the
     * check. A form added to the catalog with no skeleton does not compile, since the answer is a
     * switch over the forms; one added with a skeleton that is not a declaration fails here.
     */
    @Test
    void everyFormCanBeWrittenWithoutADeclarationToRead() {
        List<String> refused = new ArrayList<>();
        for (TopLevelForm form : TopLevelForm.values()) {
            try {
                Skeleton.Built built = Skeleton.of(DeclarationSkeletons.fixed(form));
                if (built.holes().isEmpty()) {
                    refused.add(form + " offers nothing to fill in");
                }
            } catch (Skeleton.Mismatch e) {
                refused.add(form + ": " + e.getMessage());
            }
        }
        assertEquals(List.of(), refused, "a form whose skeleton is not a declaration");
    }

    /** The one for a {@code let} states no parameters, having read no signature. */
    @Test
    void aSkeletonWithNoSignatureToReadStatesNoParametersItDidNotRead() {
        Skeleton.Built built = Skeleton.of(DeclarationSkeletons.fixed(TopLevelForm.FN));
        assertEquals("let name (param) = body\n", built.text());
        assertEquals(List.of("name", "param", "body"), holeTextsOf(built));
    }

    private static List<String> holeTextsOf(Skeleton.Built built) {
        return built.holes().stream()
                .map(hole -> built.text().substring(hole.start(), hole.end())).toList();
    }
}
