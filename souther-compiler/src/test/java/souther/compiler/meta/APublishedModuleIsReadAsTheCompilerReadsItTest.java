package souther.compiler.meta;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.Compiler;
import souther.compiler.ast.Hir;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A published module read back means what it meant where it was written, and says so in the terms
 * the compiler settles rather than in the words the author spelled.
 *
 * <p>What a comparison of two builds needs is exactly that. Whether two declarations say the same
 * thing is a question about what they mean; asked of their text it becomes a question about how they
 * were written, and every way of writing one thing differently has to be answered again by whoever
 * is asking. Here nothing is answered again: the front end reads the module and what comes back
 * carries which declaration each name reaches.
 */
class APublishedModuleIsReadAsTheCompilerReadsItTest {

    /** It writes `length` bare, which is what its import is for. */
    private static final String LIB = """
            module lib.text exposing ( Title )
            import String ( length )

            data Title = String
                invariant length(value) > 0
            """;

    /** And this one names that type without importing it, which the language allows. */
    private static final String QUALIFYING = """
            module app.uses

            data Note = { title: lib.text.Title }
            """;

    /** A bare name an import brought in is read as what it stands for. */
    @Test
    void aBareNameAnImportBroughtInIsReadAsWhatItStandsFor() {
        Hir.Module read = readingOf(universeOf(LIB), "lib.text",
                "the module is published and this compiler reads it").module();

        ValueName calls = calledByTheInvariantOf(read, "Title");
        assertInstanceOf(ValueName.Stdlib.class, calls,
                "`length` was brought in by an import and stands for a standard-library function");
        assertEquals("String", ((ValueName.Stdlib) calls).alias());
        assertEquals("length", ((ValueName.Stdlib) calls).name());
    }

    /**
     * A module named with a qualifier and never imported is read too.
     *
     * <p>A type is reachable qualified whether or not it was imported, so the modules a set of
     * declarations reaches are not the modules its import lines name.
     */
    @Test
    void aModuleReachedWithoutAnImportIsRead() {
        Map<String, ClassFileImage> both = Compiler.compileModules(List.of(LIB, QUALIFYING));
        PublishedUniverse universe = PublishedUniverse.of(ModulePath.of(both).declarations(), DefaultStdlib.get());

        readingOf(universe, "app.uses", "the module names a type of another and is read");

        readingOf(universe, "lib.text",
                "the module its field's type is declared by was read, with nothing importing it");
    }

    /** Reading one twice answers with the one reading. */
    @Test
    void aModuleIsReadOnce() {
        PublishedUniverse universe = universeOf(LIB);

        assertSame(universe.resolved("lib.text"), universe.resolved("lib.text"));
    }

    /**
     * Classes that declare nothing of that name say so as that.
     *
     * <p>Which of the two absences it is comes off the answer. It used to be a null, with whether
     * these classes carry the name at all asked of them again afterwards — so a name they say
     * nothing about and a name they carry unreadably were told apart by a second question rather
     * than by what the reading found.
     */
    @Test
    void whatIsNotPublishedIsNotRead() {
        PublishedUniverse universe = universeOf(LIB);

        assertInstanceOf(Readback.NotReady.SaysNothing.class, universe.resolved("nothing.here"),
                "these classes carry nothing of that name, which is not carrying it unreadably");
    }

    /** A module whose invariant calls a helper another module published. */
    private static final String OFFERING = """
            module example.money exposing ( Amount, scale )

            data Amount = Decimal

            let scale (a: Amount) : Decimal = a.value
            """;

    private static final String READING = """
            module example.order
            import example.money ( Amount, scale )

            data Line = { amount: Amount }
                invariant scale(amount) > 0.0m
            """;

    /**
     * A module whose declaration reads through a helper another module published.
     *
     * <p>What a module offers is a type and the rules written against it, so an invariant may call a
     * helper an import brought in. Reading that module back needs the value namespace its imports
     * bring in, not only the type namespace.
     */
    @Test
    void aDeclarationThatReadsThroughAnotherModulesHelperIsRead() {
        Map<String, ClassFileImage> classes = Compiler.compileModules(List.of(OFFERING, READING));
        PublishedUniverse universe = PublishedUniverse.of(ModulePath.of(classes).declarations(), DefaultStdlib.get());

        readingOf(universe, "example.order",
                "its invariant calls a helper `example.money` published, which the import brings in");
    }

    /** It names a type another module declares, and nothing else of it. */
    private static final String NAMING = """
            module example.line
            import example.money ( Amount )

            data Line = { amount: Amount }
            """;

    /**
     * A module reading through one these classes do not carry is not read.
     *
     * <p>The bare name its import brought in is in scope denoting nothing, which is what an author
     * being told what is wrong with the import line needs. A reader is not being told anything: what
     * it has is a field whose type is the error type, read back as a declaration of this module and
     * compared with one from a build that could see the module. So the two are told apart here, and
     * a module whose imports this set cannot answer is one this set cannot say what declares.
     */
    @Test
    void aModuleReadingThroughOneTheseClassesDoNotCarryIsNotRead() {
        Map<String, ClassFileImage> classes =
                new java.util.LinkedHashMap<>(Compiler.compileModules(List.of(OFFERING, NAMING)));
        int all = classes.size();
        classes.keySet().removeIf(binary -> binary.contains("money"));
        org.junit.jupiter.api.Assertions.assertTrue(classes.size() < all,
                "the module being withheld is one this set had");
        PublishedUniverse universe = PublishedUniverse.of(ModulePath.of(classes).declarations(), DefaultStdlib.get());

        Readback.Failure why = refusalOf(universe, "example.line");

        Readback.Failure.InvalidExposure lines = assertInstanceOf(
                Readback.Failure.InvalidExposure.class, why,
                "its import line names a module these classes do not carry");
        assertEquals(new Readback.Exposure.NoSuchModule("example.money"), lines.first(),
                "and the reason says which module, rather than the module being unreadable for"
                        + " nothing anybody can name");
        assertInstanceOf(Readback.NotReady.SaysNothing.class, universe.resolved("example.money"),
                "which is a name these classes say nothing about, not one they cannot read");
    }

    /**
     * A module whose declarations cannot be indexed is an absence here, wherever it is reached from.
     *
     * <p>Indexing refuses a name written twice, and a module read back from another build can carry
     * one: it was published under the rules of the compiler that built it. There is nobody to tell —
     * the source is not this compile's — so it is a module this reader cannot read, and a reader of
     * <em>that</em> is what this holds.
     *
     * <p>The second ask is the one that matters. This was settled at the moment a universe was
     * assembled, by catching what the indexing raised; a module named with a qualifier is asked for
     * again while some other module is being resolved, and the raise came back from a lookup, past
     * everything that answers absences. It is settled where the module is read now, and what a
     * lookup answers is what that reading left.
     */
    @Test
    void aModuleWhoseDeclarationsCannotBeIndexedIsAnAbsenceWhereverItIsReachedFrom() {
        Map<String, PublishedClasses.Declarations> published = Map.of(
                "pub.twice.$Module", moduleClass("pub.twice", List.of(), List.of("A", "B")),
                "pub.twice.A", dataClass("data Same = String"),
                "pub.twice.B", dataClass("data Same = Int"),
                "pub.naming.$Module", moduleClass("pub.naming", List.of(), List.of("Note")),
                "pub.naming.Note", dataClass("data Note = { s: pub.twice.Same }"));
        PublishedUniverse universe = PublishedUniverse.of(n -> PublishedClasses.carrying(published.get(n)), DefaultStdlib.get());

        assertInstanceOf(Readback.Failure.InvalidDeclarations.class,
                refusalOf(universe, "pub.twice"),
                "`Same` is declared twice, so it is not indexed");

        Readback<PublishedUniverse.Read> naming = assertDoesNotThrow(
                () -> universe.resolved("pub.naming"),
                "the module naming it is read back as an absence, not as a raise");
        assertInstanceOf(Readback.Failure.UnresolvedPublishedNames.class,
                assertInstanceOf(Readback.NotReady.Unreadable.class, naming).why(),
                "its field's type is declared by a module this reader cannot read, so the name"
                        + " reaches nothing");
    }

    /** {@code module} as this universe read it, which is what a reading that got to the end
     *  answers with. */
    private static PublishedUniverse.Read readingOf(PublishedUniverse universe, String module,
                                                    String why) {
        return assertInstanceOf(PublishedUniverse.Read.class,
                assertInstanceOf(Readback.Ready.class, universe.resolved(module), why).value());
    }

    /** Why {@code module} could not be read, as the arm rather than as an absence. */
    private static Readback.Failure refusalOf(PublishedUniverse universe, String module) {
        return assertInstanceOf(Readback.NotReady.Unreadable.class,
                universe.resolved(module)).why();
    }

    /** A `$Module` class carrying {@code types}, as another build would have stamped it. */
    private static PublishedClasses.Declarations moduleClass(String module, List<String> imports,
                                                            List<String> types) {
        return new PublishedClasses.Declarations(new PublishedClasses.SoutherModuleView(
                souther.compiler.codegen.Backend.BOUNDARY_VERSION, "another build",
                "module " + module + " exposing ( Same, Note )", imports, types,
                List.of(), List.of()), null, null, null);
    }

    /** The class one declaration was stamped on. */
    private static PublishedClasses.Declarations dataClass(String declaration) {
        return new PublishedClasses.Declarations(null, declaration, null, null);
    }

    /** What the invariant of {@code type} calls, as the front end answered it. */
    private static ValueName calledByTheInvariantOf(Hir.Module module, String type) {
        for (Hir.Def def : module.defs()) {
            if (def instanceof Hir.Data data && data.name().equals(type)) {
                Hir.Expr clause = data.invariants().get(0).expr();
                Hir.Apply call = (Hir.Apply) ((Hir.Binary) clause).left();
                return ((Hir.Var.Denoting) call.function()).denotes();
            }
        }
        throw new IllegalStateException("no `" + type + "` in " + module.name());
    }

    private static PublishedUniverse universeOf(String source) {
        Map<String, ClassFileImage> classes = Compiler.compile(source);
        return PublishedUniverse.of(ModulePath.of(classes).declarations(), DefaultStdlib.get());
    }
}
