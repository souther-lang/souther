package souther.compiler.meta;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.Reserved;
import souther.compiler.diag.Severity;
import souther.compiler.query.Compilation;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.query.Output;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the language declares is not something either build publishes, so a crossing does not go
 * looking for it.
 *
 * <p>The primitives, {@code Option}'s two cases and the prelude's runtime-backed data are declared
 * by no module. Nothing emits a {@code souther/$Module.class}, no artifact in
 * {@code org.souther-lang} carries one, and no model can be made to produce one — so a walk that
 * reaches one of them and asks the classes about its module is asking after an artifact that
 * cannot exist.
 * Whether two builds have the same ones is settled elsewhere and by something else: each side's
 * classes carry the boundary revision they were written at, and a set that does not agree with this
 * compiler's is refused while it is read ({@link ModuleReadback}).
 *
 * <p>What it cost is #1049. The exclusion was written as a test of the module name against the
 * standard library's <em>qualifiers</em> — {@code List}, {@code Option}, the spellings a call
 * writes — and a qualifier is never the module of a name resolution has settled, so the test was one
 * no reached thing could pass. A rule naming {@code Some} or {@code Int} in a {@code match} arm sent
 * the walk to {@code souther}, both sides answered that they carry nothing of that name, and the
 * author of the model was told to add {@code souther} to their dependencies.
 *
 * <p>Held over what is asked of the classes and not only over what comes back. An agreement that
 * comes out right while the walk still reads the language's namespace is one route away from saying
 * E1927 again, and the two spellings below already differ in which of them reaches it.
 */
class TheLanguagesOwnDeclarationsAreNotAskedOfEitherBuildTest {

    /** A rule reached from an {@code ensures} that matches on an optional: the arms name
     *  {@code Some} and {@code None}, which the language declares and no module does. */
    private static final String MATCHING = """
            module probe.opt

            data Tag = String
            data Query = { tag: Tag? }
            data Page = { tags: List<Tag> }

            behavior pick : (query: Query) -> Page
                ensures carries(query, value)

            let carries (query: Query, page: Page): Bool =
                match query.tag with
                    | None   -> true
                    | Some t -> List.contains(t, page.tags)
            """;

    /** The same rule written down the pipe, which reaches the library as a library name and never
     *  names a case. This spelling crossed while the one above did not, which is the asymmetry. */
    private static final String PIPING = """
            module probe.opt

            data Tag = String
            data Query = { tag: Tag? }
            data Page = { tags: List<Tag> }

            behavior pick : (query: Query) -> Page
                ensures carries(query, value)

            let carries (query: Query, page: Page): Bool =
                Option.withDefault(true, Option.map(t -> List.contains(t, page.tags), query.tag))
            """;

    /**
     * A helper an invariant is read through whose arms name a primitive case and a built-in error
     * case: {@code souther} and {@code souther.runtime}, the two halves of the namespace.
     *
     * <p>Here because {@code Option} was never what was wrong. Every case name the language gives
     * reaches this the same way, and {@code Int} being found first is the only reason the report
     * named {@code souther} rather than {@code souther.runtime} — excluding one of them would
     * have left the walk stopping at the other.
     */
    private static final String UNIONING = """
            module probe.uni

            import Int ( divide )

            data Amount = Int
                invariant ok(value)

            behavior half : (a: Amount) -> Amount
                constructs Amount

            let ok (v: Int): Bool =
                match divide(v, 2) with
                    | Int as q -> q >= 0
                    | DivisionByZero -> false

            let half (a) = Amount(a.value)
            """;

    /** The same model with the invariant narrowed, for what an ordinary module's declaration moving
     *  still is. */
    private static final String UNIONING_NARROWED = UNIONING.replace("q >= 0", "q >= 1");

    @Test
    void aRuleThatMatchesOnAnOptionalIsHeld() {
        assertInstanceOf(Agreement.Agree.class, heldFrom("probe.opt", "pick", MATCHING, MATCHING),
                "the arms name what the language declares, which is not a module to be read");
    }

    @Test
    void andTheSameRuleWrittenDownThePipeIsHeldAlike() {
        assertInstanceOf(Agreement.Agree.class, heldFrom("probe.opt", "pick", PIPING, PIPING),
                "which spelling a rule is written in is not a fact about what crosses");
    }

    @Test
    void aRuleThatNamesAPrimitiveCaseAndABuiltInErrorCaseIsHeld() {
        assertInstanceOf(Agreement.Agree.class, heldFrom("probe.uni", "half", UNIONING, UNIONING),
                "`Int` and `DivisionByZero` are declared by the language, not by `probe.uni`");
    }

    @Test
    void neitherSidesClassesAreAskedForAnythingTheLanguageDeclares() {
        Asked ours = new Asked(declarationsOf(UNIONING));
        Asked theirs = new Asked(declarationsOf(UNIONING));

        DeclarationAgreement.of("probe.uni", "half", ours, theirs, DefaultStdlib.get());

        assertEquals(List.of(), ours.reserved(), "the module being evaluated is not asked");
        assertEquals(List.of(), theirs.reserved(), "and neither is the answer");
        // The denominator, for both sides. An empty list of reserved names is what a crossing that
        // asked nothing at all also answers, and each side is read separately.
        assertTrue(ours.asked.contains("probe.uni.$Module"),
                () -> "that is not a crossing at all: " + ours.asked);
        assertTrue(theirs.asked.contains("probe.uni.$Module"),
                () -> "the answer's classes were never read: " + theirs.asked);
    }

    /**
     * The walk still crosses an ordinary module: leaving the language out is not leaving the
     * question out.
     *
     * <p>The helper and not the data, because the helper is what moved. An invariant carries the
     * call it writes, which is the same call on both sides; what the two say differently is the
     * body behind it, and reaching that body is the walk doing its job.
     */
    @Test
    void aDeclarationOfAnOrdinaryModuleIsStillHeld() {
        Agreement held = heldFrom("probe.uni", "half", UNIONING, UNIONING_NARROWED);

        Agreement.Disagree said = assertInstanceOf(Agreement.Disagree.class, held,
                "the rule the answer was built against admits something else");
        assertEquals("probe.uni", said.module());
        assertEquals("ok", said.declaration());
    }

    /**
     * A reserved name arriving where a module is read is this compiler's mistake, and is raised.
     *
     * <p>Not a second place the language is left out — {@code reach} decides that. What is held
     * here is that a route opened later fails where it is written, rather than reaching an author as
     * E1927 telling them to depend on something nobody ships.
     */
    @Test
    void readingAModuleOfTheLanguagesNamespaceIsRefusedRatherThanReported() {
        PublishedClasses classes = declarationsOf(UNIONING);

        IllegalStateException raised = assertThrows(IllegalStateException.class,
                () -> DeclarationAgreement.of("souther", "half", classes, classes,
                        DefaultStdlib.get()));

        assertTrue(raised.getMessage().contains("souther"), raised::getMessage);
    }

    private static Agreement heldFrom(String module, String behavior, String ours, String theirs) {
        return DeclarationAgreement.of(module, behavior, declarationsOf(ours),
                declarationsOf(theirs), DefaultStdlib.get());
    }

    /** What was asked of one side's classes, kept as it was asked. */
    private static final class Asked implements PublishedClasses {

        private final PublishedClasses of;
        private final List<String> asked = new ArrayList<>();

        private Asked(PublishedClasses of) {
            this.of = of;
        }

        @Override
        public Carried of(String binaryName) {
            asked.add(binaryName);
            return of.of(binaryName);
        }

        /** The names asked for that address something of the language's namespace. */
        private List<String> reserved() {
            return asked.stream().filter(name -> Reserved.isNamespace(moduleOf(name))).toList();
        }

        /** The module part of a binary name — everything before the last dot, which is where the
         *  class the declarations are stamped on hangs. */
        private static String moduleOf(String binaryName) {
            int dot = binaryName.lastIndexOf('.');
            return dot < 0 ? binaryName : binaryName.substring(0, dot);
        }
    }

    private static PublishedClasses declarationsOf(String source) {
        Compilation compiled = Compilation.ofSource(source, "Main");
        Map<String, ClassFileImage> classes = compiled.db().ask(new Output.All()).value();
        assertEquals(List.of(), compiled.diagnostics().values().stream().flatMap(List::stream)
                        .filter(d -> d.diagnostic().severity() == Severity.ERROR)
                        .map(d -> String.valueOf(d.diagnostic().code())).toList(),
                "the model this is measured against compiles");
        return ModulePath.of(classes).declarations();
    }
}
