package souther.compiler.meta;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Compilation;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Output;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * Whether the declarations an answer reads a row's values by are the ones the row is written for.
 *
 * <p>An implementation supplied from outside a compile was built against a module's classes as some
 * earlier build emitted them, and the rows it is held to are read now. Two builds, and nothing makes
 * them one: a project where the model is edited and only the tests are re-run puts them a revision
 * apart as a matter of course. What is asked here is whether they still say the same thing about
 * everything a value crossing between them depends on.
 *
 * <p>The question is not whether the two are the same build. A build differs from another in ways a
 * crossing cannot see — a {@code let} body, an example, the order two declarations were written in —
 * and answering with "not the same build" would report a model as one whose rows do not hold every
 * time anything at all was edited. What is compared is what the crossing depends on.
 */
class TheDeclarationsAnAnswerReadsByAreHeldToTheEvaluatedModuleTest {

    private static final String MODEL = """
            module example.stale
            import String ( length )

            data Title = String
                invariant length(value) > 0

            data Todo = { title: Title, done: Bool }

            behavior rename : (t: Todo, to: Title) -> Todo
                constructs Todo

            let rename (t, to) = Todo { title = to, done = t.done }
            """;

    /** A model spread over two modules: what a field's type is declared by is imported. */
    private static final String SHARED = """
            module example.shared exposing ( Title )
            import String ( length )

            data Title = String
                invariant length(value) > 0
            """;

    private static final String ROOT = """
            module example.root
            import example.shared ( Title )

            data Todo = { title: Title, done: Bool }

            behavior rename : (t: Todo, to: Title) -> Todo
                constructs Todo

            let rename (t, to) = Todo { title = to, done = t.done }
            """;

    /** The same model with a behavior that answers with a union, for what a case being added is. */
    private static final String UNION_MODEL = """
            module example.stale
            import String ( length )

            data Title = String
                invariant length(value) > 0

            data Todo = { title: Title, done: Bool }

            data NotFound = { title: Title }

            data Archived = { title: Title }

            data Outcome = Todo | NotFound

            behavior find : (to: Title) -> Outcome
                constructs Todo

            let find (to) = Todo { title = to, done = false }
            """;

    /**
     * Two builds of one source agree.
     *
     * <p>The compiles are separate, so nothing is shared between what is compared — this is the
     * position an implementation built by an earlier build is in, with the thing that would make it
     * stale not having happened.
     */
    @Test
    void twoBuildsOfOneSourceAgree() {
        Agreement held = DeclarationAgreement.of("example.stale",
                declarationsOf(MODEL), declarationsOf(MODEL));

        assertInstanceOf(Agreement.Agree.class, held,
                "nothing a crossing depends on differs between them");
    }

    /**
     * An invariant that has been narrowed since the answer was built.
     *
     * <p>What goes wrong without this is quiet: the row states a value the model now admits, the
     * older {@code Title} refuses it, and the run sees a value it built and cannot hand on. That
     * lands where an environment problem lands, and reads as one.
     */
    @Test
    void anInvariantNarrowedSinceTheAnswerWasBuiltIsADisagreement() {
        String narrowed = MODEL.replace("invariant length(value) > 0",
                "invariant length(value) > 3");

        Agreement held = DeclarationAgreement.of("example.stale",
                declarationsOf(narrowed), declarationsOf(MODEL));

        Agreement.Disagree said = assertInstanceOf(Agreement.Disagree.class, held,
                "an invariant is part of what a value is, so the two read the same value differently");
        assertEquals("example.stale", said.module());
        assertEquals("Title", said.declaration(), "and it says which declaration moved");
    }

    /**
     * A declaration written out differently says the same thing.
     *
     * <p>What a crossing depends on is what a declaration says, and spacing says nothing. A check
     * that reported this would report a stale build every time a file was reformatted, which is the
     * failure this exists to stop being reported for reasons nobody can act on.
     */
    @Test
    void aDeclarationSpacedDifferentlyIsNotADisagreement() {
        String spaced = MODEL
                .replace("data Todo = { title: Title, done: Bool }",
                        "data Todo = {\n    title:   Title,\n    done:    Bool\n}")
                .replace("data Title = String", "// what a todo is called\ndata Title = String");

        Agreement held = DeclarationAgreement.of("example.stale",
                declarationsOf(spaced), declarationsOf(MODEL));

        assertInstanceOf(Agreement.Agree.class, held,
                "how a declaration is written out is not something a value can be read differently by");
    }

    /**
     * A behavior's body is not part of what a value crossing into it depends on.
     *
     * <p>The body is not published — a reader has the signature and calls it — and an implementation
     * supplied from outside is a body of its own anyway. What the run finds out about a body that has
     * moved is what the rows are there to find out.
     */
    @Test
    void aBodyThatMovedIsNotADisagreement() {
        String rewritten = MODEL.replace("let rename (t, to) = Todo { title = to, done = t.done }",
                "let rename (t, to) = Todo { done = t.done, title = to }");

        Agreement held = DeclarationAgreement.of("example.stale",
                declarationsOf(rewritten), declarationsOf(MODEL));

        assertInstanceOf(Agreement.Agree.class, held,
                "a `let` body is not read by anything crossing into the answer");
    }

    /**
     * A case added to a union since the answer was built.
     *
     * <p>The quiet one. A row expects the case, the answer has no such case, and what comes back is
     * read at a case the model does not have there — which lands on a comparison, and a comparison is
     * read as a statement about the model.
     */
    @Test
    void aCaseAddedToAUnionSinceTheAnswerWasBuiltIsADisagreement() {
        // Both builds declare `Archived`; only the newer one answers with it. So what differs is the
        // union and nothing else, which is the difference a row expecting that case runs into.
        String answering = UNION_MODEL.replace("data Outcome = Todo | NotFound",
                "data Outcome = Todo | NotFound | Archived");

        Agreement held = DeclarationAgreement.of("example.stale",
                declarationsOf(answering), declarationsOf(UNION_MODEL));

        Agreement.Disagree said = assertInstanceOf(Agreement.Disagree.class, held,
                "the answer has no case for what the row expects");
        assertEquals("Outcome", said.declaration());
    }

    /**
     * A field renamed since the answer was built.
     *
     * <p>The neutral form carries the new name and the older decoder finds nothing under it.
     */
    @Test
    void aFieldRenamedSinceTheAnswerWasBuiltIsADisagreement() {
        String renamed = MODEL.replace("done: Bool", "finished: Bool")
                .replace("done = t.done", "finished = t.finished");

        Agreement held = DeclarationAgreement.of("example.stale",
                declarationsOf(renamed), declarationsOf(MODEL));

        Agreement.Disagree said = assertInstanceOf(Agreement.Disagree.class, held,
                "a decoder reads fields by name");
        assertEquals("Todo", said.declaration());
    }

    /**
     * A behavior whose signature has moved.
     *
     * <p>What a behavior takes and answers with is the whole of what crosses into it, so an answer
     * built against another signature is being handed values by a shape nothing agreed on.
     */
    @Test
    void aBehaviorSignatureThatMovedIsADisagreement() {
        String moved = MODEL.replace("behavior rename : (t: Todo, to: Title) -> Todo",
                "behavior rename : (t: Todo, to: Title, also: Bool) -> Todo")
                .replace("let rename (t, to) =", "let rename (t, to, also) =");

        Agreement held = DeclarationAgreement.of("example.stale",
                declarationsOf(moved), declarationsOf(MODEL));

        Agreement.Disagree said = assertInstanceOf(Agreement.Disagree.class, held);
        assertEquals("rename", said.declaration());
    }

    /**
     * A module reached through an import is held to as well.
     *
     * <p>A field of an imported type is read by that module's declarations, so a module whose own
     * declarations agree can still be read by an invariant from a build that has moved. What it
     * reports is the module that differs, which is the imported one and not the one the rows are
     * written for.
     */
    @Test
    void aModuleReachedThroughAnImportIsHeldToo() {
        String narrowed = SHARED.replace("invariant length(value) > 0",
                "invariant length(value) > 3");

        Agreement held = DeclarationAgreement.of("example.root",
                declarationsOf(List.of(SHARED, ROOT)), declarationsOf(List.of(narrowed, ROOT)));

        Agreement.Disagree said = assertInstanceOf(Agreement.Disagree.class, held,
                "the module the rows are written for agrees, and what it imports does not");
        assertEquals("example.shared", said.module(), "it names the module that moved");
        assertEquals("Title", said.declaration());
    }

    /** Two builds of a model spread over two modules agree, one import deep. */
    @Test
    void twoBuildsOfAModelWithAnImportAgree() {
        Agreement held = DeclarationAgreement.of("example.root",
                declarationsOf(List.of(SHARED, ROOT)), declarationsOf(List.of(SHARED, ROOT)));

        assertInstanceOf(Agreement.Agree.class, held);
    }

    /**
     * Classes that carry no declarations at all.
     *
     * <p>A jar from before modules carried them, and a name that is not a compiled Souther module,
     * arrive the same way: there is nothing to compare. Answered rather than assumed — the classes
     * may well be of exactly this module, and what is known is that nothing here can say so.
     */
    @Test
    void classesCarryingNoDeclarationsCannotBeToldEitherWay() {
        Agreement held = DeclarationAgreement.of("example.stale",
                declarationsOf(MODEL), _ -> null);

        Agreement.Unreadable said = assertInstanceOf(Agreement.Unreadable.class, held,
                "nothing was published, so nothing was established");
        assertEquals(Agreement.Reason.NOTHING_PUBLISHED, said.reason());
    }

    /**
     * A module that published declarations whose classes are not all there.
     *
     * <p>The module says which classes carry what it declared, and one of them is missing. What was
     * published cannot be read back, so whether it agrees is not something this can say.
     */
    @Test
    void declarationsThatCannotBeReadBackCannotBeToldEitherWay() {
        PublishedModule.Classes incomplete = missing("example.stale.Title",
                declarationsOf(MODEL));

        Agreement held = DeclarationAgreement.of("example.stale", declarationsOf(MODEL), incomplete);

        Agreement.Unreadable said = assertInstanceOf(Agreement.Unreadable.class, held,
                "a declaration was published and the class carrying it is not there");
        assertEquals(Agreement.Reason.NOT_READABLE_HERE, said.reason());
    }

    /** {@code classes} with {@code absent} not on it, as an incomplete jar has it. */
    private static PublishedModule.Classes missing(String absent, PublishedModule.Classes classes) {
        return binaryName -> binaryName.equals(absent) ? null : classes.of(binaryName);
    }

    /** The classes one build of a model spread over several sources emits. */
    private static PublishedModule.Classes declarationsOf(List<String> sources) {
        Compilation compiled = Compilation.ofSources(sources, ModulePath.EMPTY);
        Map<String, byte[]> classes = compiled.db().ask(new Output.All()).value();
        assertEquals(List.of(), diagnosed(compiled), "the model this is measured against compiles");
        return new ClassFileDeclarations(classes::get);
    }

    /**
     * The classes one build of {@code source} emits, read for what they were stamped with.
     *
     * <p>The build is held to compiling. What is being measured is two models that both compile
     * saying different things, and a model that did not compile stamps nothing on its classes — so a
     * broken source would arrive here as "the declarations could not be read", which is a different
     * answer that would look like the one being asked for.
     */
    private static PublishedModule.Classes declarationsOf(String source) {
        Compilation compiled = Compilation.ofSource(source, "Main");
        Map<String, byte[]> classes = compiled.db().ask(new Output.All()).value();
        assertEquals(List.of(), diagnosed(compiled), "the model this is measured against compiles");
        return new ClassFileDeclarations(classes::get);
    }

    /** What a compile said, as codes — nothing, for every model measured here. */
    private static List<String> diagnosed(Compilation compiled) {
        return compiled.diagnostics().values().stream().flatMap(List::stream)
                .map(d -> String.valueOf(d.diagnostic().code())).toList();
    }
}
