package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.ast.DefinitionName;
import souther.compiler.ast.Hir;
import souther.compiler.query.Bodies;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.OccurrenceLineage;
import souther.compiler.types.MaterialisationSite;
import souther.compiler.types.RegionSlot;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.SourceReferenceOrigin;
import souther.compiler.types.ValueName;
import souther.compiler.types.WrittenOwner;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value built for two regions is two builds of one written body, and they are two occurrences.
 *
 * <p>Everything that files an answer about a construct addresses it by what the source wrote and
 * which copies it stands in, and one enumeration of a module's comparisons refuses a place two of
 * its nodes share. A value named on paths that share no region is built once per region, so what
 * tells those builds apart has to be in the address — wherever the regions are: two behaviors, two
 * forks of one, the right of a short-circuit, and a value whose own fork names another.
 *
 * <p>The model states one rule where a value is named, however many builds the compiler made of it,
 * so the builds are two occurrences of one construct of the model.
 */
class AValueBuiltForTwoRegionsIsTwoOccurrencesTest {

    private static final String HEAD = """
            module m exposing (f, Kind, Amount)

            data Kind = Yes | No

            data Amount = Int invariant value >= 0

            let inner = List.length([1, 2, 3]) > 2

            let outer = if List.length([1]) > 0 then inner else false

            """;

    private static void accepted(String tail) {
        assertEquals("{0=[]}", String.valueOf(Compiler.compiled(HEAD + tail, "m").diagnostics()));
    }

    /** The bodies a behavior of {@code source} is lowered to, for a reader counting what stands in
     *  them. */
    private static Hir.Expr loweredBody(String source, String behavior) {
        return Compiler.compiled(source, "m").db()
                .ask(new Bodies.LoweredBody("m", new DefinitionName(behavior)))
                .value().value().writtenBody();
    }

    /** The body a behavior is read as where the language's own operations stand. */
    private static Hir.Expr analysisBody(String source, String behavior) {
        return Compiler.compiled(source, "m").db()
                .ask(new Bodies.BodyForInvariantDischarge("m", behavior))
                .value().value().writtenBody();
    }

    /** The regions {@code e} holds a build of {@code inner} for. */
    private static List<MaterialisationSite> buildsOfInner(Hir.Expr e) {
        List<MaterialisationSite> out = new ArrayList<>();
        collect(e, name -> name.endsWith("inner"), out);
        return out;
    }

    /** The regions {@code e} holds a build for, of each value whose name {@code of} answers for. */
    private static void collect(Hir.Expr e, Predicate<String> of, List<MaterialisationSite> out) {
        if (e == null) {
            return;
        }
        if (e instanceof Hir.Materialised built && of.test(built.value().toString())) {
            out.add(built.site());
        }
        // A build the tree an analysis reads holds by reference is a build all the same.
        if (e instanceof Hir.ValueBuild built && of.test(built.value().toString())) {
            out.add(built.site());
        }
        Hir.forEachChild(e, child -> collect(child, of, out));
    }

    /**
     * Two behaviors that each name one value, which is the least a second build takes.
     *
     * <p>Each names it at the head of its own body, so the two builds are told apart by the
     * definition the body is of and by nothing else — the one thing a fork, an arm or a block is
     * not there to supply.
     */
    @Test
    void twoBehaviorsThatEachNameOneValue() {
        String source = HEAD + """
                behavior f : (n: Int) -> Bool
                let f (n) = inner

                behavior g : (n: Int) -> Bool
                let g (n) = inner
                """;
        assertEquals("{0=[]}", String.valueOf(Compiler.compiled(source, "m").diagnostics()));

        assertEquals(List.of(new MaterialisationSite.Body(new WrittenOwner.Body("m", "f"))),
                buildsOfInner(loweredBody(source, "f")));
        assertEquals(List.of(new MaterialisationSite.Body(new WrittenOwner.Body("m", "g"))),
                buildsOfInner(loweredBody(source, "g")));
    }

    /** A value the root region demands and a fork inside it names as well is one build, at the
     * root: the template the analysis reads takes it once and the fork reads that, rather than
     * building it a second time for the region it names it in. */
    @Test
    void aValueNamedAtTheRootAndInsideAForkIsBuiltOnceAtTheRoot() {
        String source = """
                module m exposing (f)

                let inner = List.length([1, 2, 3]) > 2

                let outer = inner && (if List.length([1]) > 0 then inner else false)

                behavior f : (n: Int) -> Bool
                let f (n) = outer
                """;

        List<MaterialisationSite> builds = buildsOfInner(analysisBody(source, "outer"));

        assertEquals(1, builds.size(), builds.toString());
        assertTrue(builds.getFirst() instanceof MaterialisationSite.Body, builds.toString());
    }

    @Test
    void oneValueNamedInAnArmOfEachOfTwoForks() {
        accepted("""
                behavior f : (n: Int) -> Bool
                let f (n) = (if n > 0 then inner else false) || (if n > 1 then inner else false)
                """);
    }

    @Test
    void oneValueNamedOnTheRightOfTwoShortCircuits() {
        accepted("""
                behavior f : (n: Int) -> Bool
                let f (n) = (n > 0 && inner) || (n > 1 && inner)
                """);
    }

    @Test
    void oneValueNamedInAnArmOfEachOfTwoMatches() {
        accepted("""
                behavior f : (k: Kind) -> Bool
                let f (k) =
                  (match k with | Yes -> inner | No -> false)
                  || (match k with | Yes -> false | No -> inner)
                """);
    }

    @Test
    void oneValueNamedInAnArmOfEachOfTwoAttemptedConstructions() {
        accepted("""
                behavior f : (n: Int) -> Bool
                let f (n) =
                  (if Amount(n) as a then inner else false)
                  || (if Amount(n - 1) as b then false else inner)
                """);
    }

    @Test
    void aValueInAComprehensionGuardAndInAnArm() {
        accepted("""
                behavior f : (n: Int) -> Bool
                let f (n) =
                  List.length([n | inner, n > 0]) > 0 || (if n > 1 then inner else false)
                """);
    }

    @Test
    void aValueWhoseOwnForkNamesAnotherBuiltForTwoRegions() {
        accepted("""
                behavior f : (n: Int) -> Bool
                let f (n) = (if n > 0 then outer else false) || (if n > 1 then outer else false)
                """);
    }


    /**
     * A value named inside a block this compiler wrote out of a name is built there, and the block
     * is told by the name it was written out of.
     *
     * <p>A name standing where a value goes is the function it names, and what a pass puts there is
     * the block applying it — whose body is entered per application, so a value the applied helper
     * names is built inside it. Which block that is, is said where the block is written: the call
     * inside it is expanded afterwards, so a reader working it out from the shape the block ended up
     * with is asking a question the shape stopped answering.
     *
     * <p>Read off the reading where the operation stands. Expanded, the block is spliced into the
     * operation's own body and what the build stands in is a region that body opens — which is the
     * two readings copying different things, and not the two disagreeing.
     */
    @Test
    void aValueNamedInsideABlockWrittenOutOfANameIsBuiltThere() {
        String source = """
                module m exposing (f)

                let limit = List.length([1, 2, 3])

                let big (n: Int) : Bool = n > limit

                behavior f : (xs: List<Int>) -> Bool
                let f (xs) = List.any(big, xs)
                """;
        assertEquals("{0=[]}", String.valueOf(Compiler.compiled(source, "m").diagnostics()));

        List<MaterialisationSite> built = new ArrayList<>();
        collect(analysisBody(source, "f"), each -> each.endsWith("limit"), built);
        assertEquals(List.of(new MaterialisationSite.GeneratedBlock(
                        new SourceReferenceOrigin(new WrittenOwner.Body("m", "f"), 0))),
                built);
    }

    private static final WrittenOwner.Body OWNER = new WrittenOwner.Body("m", "f");

    private static final ValueName VALUE = new ValueName.Helper("m", "inner");

    private static MaterialisationSite armOf(int fork, RegionSlot slot) {
        return new MaterialisationSite.Slot(
                SourceConstructOrigin.written(OWNER, fork, SourceConstruct.IF), slot);
    }

    private static ConstructOccurrence builtFor(MaterialisationSite site) {
        return new ConstructOccurrence(
                SourceConstructOrigin.written(new WrittenOwner.Body("m", "inner"), 0,
                        SourceConstruct.BINARY),
                OccurrenceLineage.ORIGINAL.builtFor(VALUE, site));
    }

    @Test
    void twoBuildsOfOneConstructAreTwoOccurrences() {
        ConstructOccurrence first = builtFor(armOf(0, new RegionSlot.IfThen()));
        ConstructOccurrence second = builtFor(armOf(1, new RegionSlot.IfThen()));

        assertNotEquals(first, second);
    }

    @Test
    void theModelStatesOneConstructWhereTwoBuildsWereMade() {
        ConstructOccurrence first = builtFor(armOf(0, new RegionSlot.IfThen()));
        ConstructOccurrence second = builtFor(armOf(1, new RegionSlot.IfThen()));

        assertEquals(ModelOccurrence.statedAt(first), ModelOccurrence.statedAt(second));
    }
}
