package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.ast.Ast;
import souther.compiler.check.Sig;
import souther.compiler.examples.EvaluationPolicy;
import souther.compiler.generated.GeneratedBehavior;
import souther.compiler.generated.JsonBoundary;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import tools.jackson.databind.json.JsonMapper;

import java.time.Duration;
import java.util.ArrayList;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A class is its binary name and the loader that defined it, so what a compilation answers when it
 * is asked for its loader twice decides whether a value one of its behaviors made is a value the
 * next one can be handed. Two loaders are two definitions of every type it generated, and the way
 * that shows is not an exception: a decoded key stops equalling the key a behavior looks up, the
 * lookup misses, and the behavior answers with its default — reported as a model that is wrong
 * (issue #685).
 *
 * <p>What the loader is kept against is the classes and not the compilation. Asking a compilation a
 * question is what makes the work that answers it, so there is no point at which it becomes settled
 * and none at which a loader could be taken too early; and an edit that reaches the generation makes
 * a different program, which a loader held across it could not see. The rows below say both halves:
 * an input the classes do not read leaves the loader alone, and one that changes them replaces it.
 */
final class ACompilationAnswersWithOneLoaderForItsClassesTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String SOURCE = """
            module demo
            data Key = String
            behavior at : (m: Map<Key, Int>) -> Int
            let at (m) = Option.withDefault(0, Map.get(Key("a"), m))
            """;

    @Test
    void askedTwiceItIsOneLoader() {
        Compilation compilation = Compiler.compiled(SOURCE, "demo", new ArrayList<>());
        assertSame(compilation.loader(), compilation.loader(), "the loader, asked twice");
    }

    /**
     * The budget, the policy and what is measured are read by the evaluation of a row and by the
     * report about it. None of them is read on the way to {@code Output.Classes}, so none of them
     * makes a different program — and a loader replaced by one of them would divide the types over a
     * setting that did not reach them.
     */
    @Test
    void anInputTheClassesDoNotReadLeavesItAlone() {
        Compilation compilation = Compiler.compiled(SOURCE, "demo", new ArrayList<>());
        ClassLoader before = compilation.loader();

        // Each of these is a value this compilation did not already hold, so each is a real change
        // to an input rather than a set that answers the same and stops there.
        compilation.withExampleBudget(Duration.ofMillis(12_345));
        compilation.withEvaluationPolicy(new EvaluationPolicy(999_999L,
                EvaluationPolicy.DEFAULT_RECURSION_DEPTH_LIMIT,
                EvaluationPolicy.DEFAULT_OUTER_TIMEOUT,
                EvaluationPolicy.DEFAULT_WORKER_STACK_BYTES));
        compilation.measure(Adequacy.Asked.warningsAt(Adequacy.Level.ALL));

        assertSame(before, compilation.loader(), "the loader after an input the classes do not read");
    }

    /** A workspace handed over again unchanged — what an editor does on a keystroke that undoes
     *  itself — is not an edit, so what was generated is what there is. */
    @Test
    void aWorkspaceHandedOverUnchangedLeavesItAlone() {
        Compilation compilation = Compilation.ofDocuments(
                Map.of("a.sou", SOURCE), Set.of(), ModulePath.EMPTY);
        ClassLoader before = compilation.loader();
        compilation.update(Map.of("a.sou", SOURCE), Set.of());
        assertSame(before, compilation.loader(), "the loader after an update that changed nothing");
    }

    @Test
    void anEditThatReachesTheClassesReplacesIt() {
        Compilation compilation = Compilation.ofDocuments(
                Map.of("a.sou", SOURCE), Set.of(), ModulePath.EMPTY);
        ClassLoader before = compilation.loader();
        compilation.update(Map.of("a.sou", SOURCE.replace("Key(\"a\")", "Key(\"b\")")), Set.of());
        assertNotSame(before, compilation.loader(), "the loader after an edit");
    }

    /**
     * The whole of it, said as the one rule rather than as a list of the edits it was tried on: the
     * loader stands exactly while the classes do.
     *
     * <p>Whether a particular edit reaches the classes is not this method's question and not a claim
     * these rows make. An edit and its undo, with nothing asked in between, is absorbed above the
     * generation — the module re-parses to an answer equal to the one kept, so nothing below it is
     * recomputed and the classes are the classes. Asked in between, the kept answer is the edited
     * one, going back differs from it, and the classes are generated again. Both are the store
     * deciding what changed, and either is right here: what may not happen is a loader that is not
     * over what {@link Compilation#classes()} now answers, or a second one over classes that never
     * moved.
     */
    @Test
    void itStandsExactlyWhileTheClassesDo() {
        String edited = SOURCE.replace("Key(\"a\")", "Key(\"b\")");
        for (boolean lookingInBetween : new boolean[] {true, false}) {
            Compilation compilation = Compilation.ofDocuments(
                    Map.of("a.sou", SOURCE), Set.of(), ModulePath.EMPTY);
            Map<String, byte[]> classes = compilation.classes();
            ClassLoader loader = compilation.loader();

            compilation.update(Map.of("a.sou", edited), Set.of());
            if (lookingInBetween) {
                classes = sameOrNot(compilation, classes, loader, "the edit");
                loader = compilation.loader();
            }

            compilation.update(Map.of("a.sou", SOURCE), Set.of());
            sameOrNot(compilation, classes, loader, "the undo, looking=" + lookingInBetween);
        }
    }

    /** Asserts the rule at one step and answers with the classes as they now are. */
    private static Map<String, byte[]> sameOrNot(Compilation compilation,
                                                 Map<String, byte[]> classesBefore,
                                                 ClassLoader loaderBefore, String step) {
        Map<String, byte[]> classesNow = compilation.classes();
        ClassLoader loaderNow = compilation.loader();
        assertEquals(classesBefore == classesNow, loaderBefore == loaderNow,
                "the loader stands exactly while the classes do, after " + step);
        return classesNow;
    }

    /** And the case that has to replace it, on its own, so the rule above is not the only thing
     *  saying that replacement ever happens. */
    @Test
    void anEditObservedAndThenUndoneReplacesIt() {
        Compilation compilation = Compilation.ofDocuments(
                Map.of("a.sou", SOURCE), Set.of(), ModulePath.EMPTY);
        ClassLoader first = compilation.loader();
        compilation.update(Map.of("a.sou", SOURCE.replace("Key(\"a\")", "Key(\"b\")")), Set.of());
        compilation.loader();
        compilation.update(Map.of("a.sou", SOURCE), Set.of());
        assertNotSame(first, compilation.loader(), "the loader after an edit that was undone");
    }

    /**
     * The failure the whole of this is about, driven the way {@code souther run} drives one: read the
     * input through a loader the compilation answered with, apply the behavior through a loader it
     * answered with again. Before #685 the key decoded by the first was not the key the second's
     * behavior looked up, and the answer came back as 0.
     */
    @Test
    void aValueReadThroughOneAskIsAValueOfTheNext() throws Exception {
        Compilation compilation = Compiler.compiled(SOURCE, "demo", new ArrayList<>());
        Ast.Module written = compilation.module(compilation.modules().get(0));
        Sig sig = compilation.signatures(written.name()).get("at");

        ClassLoader reading = compilation.loader();
        ClassLoader applying = compilation.loader();

        Object argument = ((JsonBoundary.Read.Value) JsonBoundary.read(
                reading, sig.ins().get(0), JSON.readTree("{\"a\": 7}"))).value();
        Object answer = GeneratedBehavior.apply(applying, written.name(), "at",
                new Object[] {argument});

        assertEquals("7", JSON.writeValueAsString(
                        JsonBoundary.write(applying, written.name(), "at", sig.out(), answer)),
                "the input said 7, and the behavior looks up the key it was written under");
    }
}
