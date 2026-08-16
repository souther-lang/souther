package souther.compiler.check;

import souther.compiler.diag.Located;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.source.SourceId;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What an import line means is settled once, and each namespace reads that answer.
 *
 * <p>The answer used to be a local of the walk that assembled the scope: projected into the two
 * namespaces and dropped, so every pass that needed to know what an import brought in had the lines
 * and worked it out again. They did not agree. A module that declares a behavior and does not offer
 * it was refused where the scope is assembled and borrowed anyway where signatures are collected,
 * so an author was told the module does not expose the name and then told two modules were offering
 * it.
 *
 * <p>Nor could one answer per spelling say what a collision with a declaration written here leaves
 * behind. A data brought in under a spelling this module writes a {@code let} for is one arrival in
 * two namespaces: the {@code let} takes it as a value, and the data is still what the type means,
 * so a field written with that type is not a second thing said about the line already refused.
 * Projected from a single meaning, one of the two lost — and which one followed from the order the
 * value lookup happened to try its rungs in.
 */
class WhatAnImportMeansIsSettledOncePerNamespaceTest {

    /** What was said about {@code own.sou}, as the message each report carries. */
    private static List<String> saidAbout(Map<String, String> byId) {
        Compilation compilation = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        List<String> said = new ArrayList<>();
        for (Located each : compilation.diagnostics().get(new SourceId("own.sou"))) {
            said.add(each.diagnostic().said().getClass().getSimpleName());
        }
        return said;
    }

    private static Map<String, String> docs(String... pairs) {
        Map<String, String> byId = new LinkedHashMap<>();
        for (int i = 0; i < pairs.length; i += 2) {
            byId.put(pairs[i], pairs[i + 1]);
        }
        return byId;
    }

    /**
     * One module declares a behavior and does not offer it; another declares and offers one of the
     * same name. Importing both is one mistaken line, not a contest.
     *
     * <p>A pass that walks the lines and asks each module whether it declares a behavior of the
     * name answers yes for both, because declaring one and offering it are different questions.
     * What the lines were left with is one behavior, and every pass reads that.
     */
    @Test
    void aClaimThatDoesNotStandIsNotBorrowedEither() {
        assertEquals(List.of("TheModuleDoesNotExposeIt"), saidAbout(docs(
                "a.sou", """
                        module app.a exposing ( In )
                        data In = { n: Int }
                        behavior f : (i: In) -> In constructs In
                        let f (i) = In { n = i.n }
                        """,
                "b.sou", """
                        module app.b exposing ( In2, f )
                        data In2 = { n: Int }
                        behavior f : (i: In2) -> In2 constructs In2
                        let f (i) = In2 { n = i.n }
                        """,
                "own.sou", """
                        module app.own exposing ( Out )
                        import app.a ( f )
                        import app.b ( f, In2 )
                        data Out = { n: Int }
                        """)),
                "the module that does not offer it did not bring it in, here or anywhere else");
    }

    /**
     * A data brought in under a spelling this module writes a {@code let} for, used both ways.
     *
     * <p>The collision is reported on the line, once. What each namespace does afterwards is what
     * the author would read: the field's type is the data that was imported, and the call is the
     * {@code let} written here. Said any other way, one mistaken line costs a second report about
     * a field or a call that is right.
     */
    @Test
    void aCollisionLeavesEachNamespaceWithWhatItHas() {
        assertEquals(List.of("ImportedNameCollidesWithADeclaration"), saidAbout(docs(
                "other.sou", """
                        module app.other exposing ( Thing )
                        data Thing = { n: Int }
                        """,
                "own.sou", """
                        module app.own
                        import app.other ( Thing )
                        let Thing (x: Int): Int = x
                        data Line = { a: Thing }
                        let use (n: Int): Int = Thing(n)
                        """)),
                "the type is the one imported, the call is the one written here");
    }

    /**
     * A behavior reached through its module beside one an import line brought in.
     *
     * <p>The qualified reference names its module, so nothing about what it denotes is in doubt and
     * no contest sees it. What the two cannot both have is the member name in the generated class,
     * and that is said where the reference is written rather than at the module header, which is
     * where the import recording the dependency was synthesized.
     */
    @Test
    void aQualifiedReferenceIsNotAClaimOnTheBareName() {
        assertEquals(List.of(), saidAbout(docs(
                "other.sou", """
                        module app.other exposing ( In, Mid, quote )
                        data In = { n: Int }
                        data Mid = { n: Int }
                        behavior quote : (i: In) -> Mid constructs Mid
                        let quote (i) = Mid { n = i.n }
                        """,
                "third.sou", """
                        module app.third exposing ( Mid, other )
                        data Mid = { n: Int }
                        behavior other : (i: app.other.Mid) -> Mid constructs Mid
                        let other (i) = Mid { n = i.n }
                        """,
                "own.sou", """
                        module app.own exposing ( Out, flow : Out )
                        import app.other ( quote )
                        data Out = { n: Int }
                        behavior plus : (m: app.third.Mid) -> Out constructs Out
                        let plus (m) = Out { n = m.n + 1 }
                        behavior flow = quote >-> app.third.other >-> plus
                        """)),
                "a bare name and a qualified reference of different names are no contest at all");
    }

    /** A data and a behavior of one spelling, from two modules: two meanings, so neither. */
    @Test
    void aDataAndABehaviorOfOneSpellingLeaveTheSpellingMeaningNeither() {
        assertEquals(List.of("TheNameIsImportedFromTwoModules"), saidAbout(docs(
                "a.sou", """
                        module app.a exposing ( X )
                        data X = { n: Int }
                        """,
                "b.sou", """
                        module app.b exposing ( In, X )
                        data In = { n: Int }
                        behavior X : (i: In) -> In constructs In
                        let X (i) = In { n = i.n }
                        """,
                "own.sou", """
                        module app.own exposing ( Out )
                        import app.a ( X )
                        import app.b ( X )
                        data Out = { n: Int }
                        """)),
                "said on the line that made the contest, and nowhere the name is written");
    }

    /**
     * A refused claim and a standing one under one spelling.
     *
     * <p>The refused line is told what is wrong with it. The spelling means what the line that
     * could do its job brought in, so a use of it is not a second report — one line was mistaken,
     * and it is the one that is named.
     */
    @Test
    void aRefusedClaimBesideAStandingOneLeavesTheStandingOne() {
        assertEquals(List.of("TheModuleDoesNotExposeIt"), saidAbout(docs(
                "a.sou", """
                        module app.a exposing ( Other )
                        data Other = { n: Int }
                        let twice (x: Int): Int = x * 2
                        """,
                "b.sou", """
                        module app.b exposing ( twice )
                        let twice (x: Int): Int = x * 3
                        """,
                "own.sou", """
                        module app.own
                        import app.a ( twice )
                        import app.b ( twice )

                        let use (n: Int): Int = twice(n)
                        """)),
                "one line could not do its job, and the other one did");
    }
}
