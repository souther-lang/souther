package souther.compiler;

import souther.compiler.ast.Hir;
import souther.compiler.ast.WrittenName;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.DiagnosticPlace;
import souther.compiler.diag.LabeledRegion;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.diag.SourceProvenance;
import souther.compiler.diag.msg.NameMessage;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A binding applied where it is not a function is reported as one, and where the same spelling
 * reaches something outside the binding, the report points at what the binding hid.
 *
 * <p>What was hidden is settled where the name is read, so these are asked of whole compilations:
 * the reading is the only place that knows, and the report is the only place that says.
 */
class AnAppliedBindingSaysWhatItHidesTest {

    private static CompileException refused(String... sources) {
        return assertThrows(CompileException.class, () -> Compiler.compileModules(List.of(sources)));
    }

    private static LabeledRegion theOneLabel(CompileException e) {
        assertInstanceOf(NameMessage.ItIsNotAFunctionHere.class, e.diagnostic().said(),
                "the report is the one a binding that is not a function gets");
        assertEquals(1, e.diagnostic().secondary().size(), () -> "one label: " + e.getMessage());
        return e.diagnostic().secondary().get(0);
    }

    /** The line and column {@code label} points at in {@code source}. */
    private static String pointsAt(String source, LabeledRegion label) {
        Region region = assertInstanceOf(DiagnosticPlace.InSource.class, label.place(),
                "the hidden code is in this compilation").region();
        var at = WhereItSits.in(source, region).start();
        return at.line() + ":" + at.column();
    }

    @Test
    void aParameterThatHidesAHelperPointsAtTheHelper() {
        String source = """
                module probe.shadow exposing ( run )

                behavior run : (n: Int) -> Int
                partial let count (k: Int): Int = if k <= 0 then 0 else count(k - 1)
                let use (count: Int): Int = count(2)
                let run (n) = use(n)
                """;
        LabeledRegion label = theOneLabel(refused(source));

        assertEquals(new NameMessage.ABindingInScopeHidesIt("count", "count"), label.said());
        assertEquals("4:13", pointsAt(source, label), "the name the helper is declared under");
    }

    @Test
    void aNameThatHidesNothingKeepsTheReportItHad() {
        CompileException e = refused("""
                module probe.shadow exposing ( run )

                behavior run : (n: Int) -> Int
                partial let count (k: Int): Int = if k <= 0 then 0 else count(k - 1)
                let use (other: Int): Int = other(2)
                let run (n) = use(n)
                """);

        assertInstanceOf(NameMessage.ItIsNotAFunctionHere.class, e.diagnostic().said());
        assertEquals(List.of(), e.diagnostic().secondary());
    }

    @Test
    void aLetInsideABodyHidesAHelperTheSameWay() {
        String source = """
                module probe.shadow exposing ( run )

                behavior run : (n: Int) -> Int
                let count (k: Int): Int = k + 1
                let run (n) = {
                    let count = n
                    count(2)
                }
                """;
        LabeledRegion label = theOneLabel(refused(source));

        assertEquals(new NameMessage.ABindingInScopeHidesIt("count", "count"), label.said());
        assertEquals("4:5", pointsAt(source, label));
    }

    /** A value of the module is checked by its own reading, and says the same. */
    @Test
    void aLetInsideAValueHidesAHelperTheSameWay() {
        String source = """
                module probe.shadow exposing ( run, start )

                behavior run : (n: Int) -> Int
                let count (k: Int): Int = k + 1
                let start : Int = {
                    let count = 1
                    count(2)
                }
                let run (n) = n
                """;
        LabeledRegion label = theOneLabel(refused(source));

        assertEquals(new NameMessage.ABindingInScopeHidesIt("count", "count"), label.said());
        assertEquals("4:5", pointsAt(source, label));
    }

    /** A behavior a helper cannot reach is hidden all the same; the label says hidden and no more. */
    @Test
    void aParameterThatHidesABehaviorPointsAtTheBehavior() {
        String source = """
                module probe.shadow exposing ( run )

                behavior run : (n: Int) -> Int
                behavior count : (k: Int) -> Int
                let count (k) = k
                let use (count: Int): Int = count(2)
                let run (n) = use(n)
                """;
        LabeledRegion label = theOneLabel(refused(source));

        assertEquals(new NameMessage.ABindingInScopeHidesIt("count", "count"), label.said());
        assertEquals("4:10", pointsAt(source, label), "the behavior line, which says what it is");
    }

    private static final String LIB = """
            module probe.lib exposing ( count )


            let count (k: Int): Int = k + 1
            """;

    private static final String IMPORTING = """
            module probe.app exposing ( run )
            import probe.lib ( count )

            behavior run : (n: Int) -> Int
            let use (count: Int): Int = count(2)
            let run (n) = use(n)
            """;

    @Test
    void aHelperAnImportBroughtInIsPointedAtWhereItsModuleDeclaresIt() {
        LabeledRegion label = theOneLabel(refused(LIB, IMPORTING));

        assertEquals(new NameMessage.ABindingInScopeHidesIt("count", "probe.lib.count"),
                label.said());
        assertEquals("4:5", pointsAt(LIB, label));
    }

    /** Read back off the path, the module has no text this compilation holds, and the label says
     *  where the code came from instead of pointing. */
    @Test
    void aHelperOfAPublishedModuleIsNamedWhereItCameFrom() {
        Map<String, ClassFileImage> published = Compiler.compileModules(List.of(LIB));
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(IMPORTING), ModulePath.of(published)));
        LabeledRegion label = theOneLabel(e);

        assertEquals(new NameMessage.ABindingInScopeHidesIt("count", "probe.lib.count"),
                label.said());
        assertEquals(new DiagnosticPlace.Unavailable(
                        new SourceProvenance.APublishedModule("probe.lib", "probe.lib.count")),
                label.place());
    }

    @Test
    void aLibraryOperationAnImportBroughtInIsNamedAsTheLibraryPublishesIt() {
        LabeledRegion label = theOneLabel(refused("""
                module probe.app exposing ( run )
                import List ( map )

                behavior run : (n: Int) -> Int
                let use (map: Int): Int = map(2)
                let run (n) = use(n)
                """));

        assertEquals(new NameMessage.ABindingInScopeHidesIt("map", "List.map"), label.said());
        assertEquals(new DiagnosticPlace.Unavailable(
                        new SourceProvenance.TheStandardLibrary("souther.list", "List.map")),
                label.place());
    }

    /**
     * A library name the library rewrites into another call has no declaration of its own. The
     * label names it and the module its qualifier names, and not the declaration it rewrites to,
     * which is a different name.
     */
    @Test
    void aLibraryNameThatIsARewriteIsNamedAndNotTheCallItBecomes() {
        LabeledRegion label = theOneLabel(refused("""
                module probe.app exposing ( run )
                import List ( fold )

                behavior run : (n: Int) -> Int
                let use (fold: Int): Int = fold(2)
                let run (n) = use(n)
                """));

        assertEquals(new NameMessage.ABindingInScopeHidesIt("fold", "List.fold"), label.said());
        assertEquals(new DiagnosticPlace.Unavailable(
                        new SourceProvenance.TheStandardLibrary("souther.list", "List.fold")),
                label.place());
    }

    private static final SourcePos AT = new SourcePos(3, 7);

    /** A body copied into a file it was not read in keeps what its applied names hid: what was
     *  hidden is a reference, and the copy moves only where things are written. */
    @Test
    void aCopyOfTheApplicationKeepsWhatItHid() {
        Hir.Shadowing hid = new Hir.Shadowing.Hides(
                new ReachName.OfModule(new ValueName.Helper("probe.lib", "count")));
        Hir.AppliedCallee applied = new Hir.AppliedCallee(
                WrittenName.synthetic("count", AT), Region.point(AT), hid);

        assertEquals(hid, applied.restamped(new SourcePos(9, 1), null).shadowing());
    }
}
