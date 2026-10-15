package souther.compiler.query;

import souther.compiler.Compiler;
import souther.compiler.DefaultStdlib;
import souther.compiler.diag.msg.ModuleMessage;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.jvm.LinkageProjection;
import souther.compiler.jvm.LinkageTarget;
import souther.compiler.meta.ModulePath;
import souther.compiler.meta.ModuleReadback;
import souther.compiler.meta.ReadableModule;
import souther.compiler.meta.Readback;
import souther.compiler.types.TypeKey;

import org.junit.jupiter.api.Test;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * How a declared type's values are compared as the JVM holds them is a fact of its projection, and
 * a class that compares by it is built against that projection and not against the declarations
 * under it.
 *
 * <p>A newtype's {@code compareTo} hands the comparison to what it wraps: to that value's own
 * {@code compareTo}, or to the {@code __order} of the enumeration that lists it. Which of the two,
 * and whether there is one at all, is read off the projection of the name it wraps, so a change
 * further down reaches a module built against it only through that one projection moving.
 */
class AnOrderIsReadOffTheProjectionOfWhatIsWrappedTest {

    private static final String ONE_MODULE = """
            module m
            data Yen = Int
            data Price = Yen
            data Flag = Bool
            data Opening
            data Closing
            data Stage = Opening | Closing
            data Phase = Stage
            data Shared
            data OnlyFirst
            data OnlySecond
            data First = Shared | OnlyFirst
            data Second = Shared | OnlySecond
            data Pair = { left: Int, right: Int }
            """;

    /**
     * What each declaration says it is compared by: its own {@code compareTo} where it is a newtype
     * over something ordered, the enumeration that lists it where exactly one does, and nothing
     * otherwise — a unit two enumerations list included, since they place it differently.
     */
    @Test
    void eachDeclarationSaysWhatItIsComparedBy() {
        Compilation compilation = Compilation.ofSources(List.of(ONE_MODULE),
                ModulePath.of(Map.of()));
        Linkages.Of provided = compilation.db().ask(new Linkages.Provided("m")).value();

        Map<String, String> orderedAs = new LinkedHashMap<>();
        provided.provides().forEach((target, projection) -> {
            if (projection instanceof LinkageProjection.Data data) {
                String said = null;
                for (LinkageProjection.Fact fact : data.facts()) {
                    if (fact.label().equals("ordered as")) {
                        said = fact.value();
                    }
                }
                orderedAs.put(data.key().name(), said == null ? "-" : said);
            }
        });

        Map<String, String> expected = new LinkedHashMap<>();
        expected.put("Closing", "by m.Stage");
        expected.put("First", "by m.First");
        expected.put("Flag", "-");
        expected.put("OnlyFirst", "by m.First");
        expected.put("OnlySecond", "by m.Second");
        expected.put("Opening", "by m.Stage");
        expected.put("Pair", "-");
        expected.put("Phase", "natural");
        expected.put("Price", "natural");
        expected.put("Second", "by m.Second");
        expected.put("Shared", "-");
        expected.put("Stage", "by m.Stage");
        expected.put("Yen", "natural");
        assertEquals(expected, orderedAs);
    }

    /**
     * A newtype over a newtype of another module, itself over a newtype of a third. Its class is
     * built against the name it wraps, which says whether that name's class is ordered, and not
     * against what that name wraps in turn.
     */
    @Test
    void aNewtypeIsBuiltAgainstTheNameItWrapsAndNotTheNamesUnderIt() {
        Map<String, ClassFileImage> classes = new HashMap<>(Compiler.compile("""
                module lib.c exposing ( Level )
                data Level = Int
                """));
        classes.putAll(Compiler.compileModules(List.of("""
                module lib.b exposing ( Rank )
                import lib.c ( Level )
                data Rank = Level
                """), ModulePath.of(classes)));
        classes.putAll(Compiler.compileModules(List.of("""
                module lib.a exposing ( Grade )
                import lib.b ( Rank )
                data Grade = Rank
                """), ModulePath.of(classes)));

        assertEquals(Set.of(new LinkageTarget.Data(new TypeKey("lib.b", "Rank"))),
                readBack("lib.a", classes).requires().keySet());
    }

    /**
     * A newtype over a case of an enumeration of another module is built against the case, whose
     * projection says which enumeration places it, and against that enumeration, whose
     * {@code __order} its {@code compareTo} calls. Not against the enumeration's other cases: what
     * makes it an enumeration is said by its own projection.
     */
    @Test
    void aNewtypeOverACaseIsBuiltAgainstTheCaseAndTheEnumerationItCalls() {
        Map<String, ClassFileImage> classes = new HashMap<>(Compiler.compile(STAGES));
        classes.putAll(Compiler.compileModules(List.of(B_OVER_OPENING), ModulePath.of(classes)));

        assertEquals(Set.of(new LinkageTarget.Data(new TypeKey("lib.c", "Opening")),
                        new LinkageTarget.Data(new TypeKey("lib.c", "Stage"))),
                readBack("lib.b", classes).requires().keySet());
    }

    /**
     * The case a module's newtype wraps stops being ordered when another case of its enumeration
     * becomes a product. The module was built against the case and the enumeration and not that
     * other case, and is held to the change by what each of the two now says it is ordered as.
     */
    @Test
    void aCaseThatStopsBeingOrderedIsSaidOfTheModuleThatWrapsIt() {
        Map<String, ClassFileImage> path = new HashMap<>(Compiler.compileModules(
                List.of(B_OVER_OPENING), ModulePath.of(Compiler.compile(STAGES))));
        path.putAll(Compiler.compile("""
                module lib.c exposing ( Stage, Opening, Closing )
                data Opening
                data Closing = { at: Int }
                data Stage = Opening | Closing
                """));

        Compilation compilation = Compilation.ofSources(List.of("""
                module app.u
                import lib.b ( inc )
                behavior twice : (n: Int) -> Int
                let twice (n) = inc(inc(n))
                """), ModulePath.of(path));
        compilation.answerEverything();
        Set<ModuleMessage.ItWasBuiltAgainstAnotherLinkage> moved = new HashSet<>();
        for (Db.Found found : compilation.db().allReports()) {
            if (found.report().diagnostic().said()
                    instanceof ModuleMessage.ItWasBuiltAgainstAnotherLinkage m) {
                moved.add(m);
            }
        }

        assertEquals(Set.of(
                new ModuleMessage.ItWasBuiltAgainstAnotherLinkage("lib.b", "data", "Opening",
                        "lib.c", "ordered as", "by lib.c.Stage", "—"),
                new ModuleMessage.ItWasBuiltAgainstAnotherLinkage("lib.b", "data", "Stage",
                        "lib.c", "ordered as", "by lib.c.Stage", "—")), moved);
    }

    private static final String STAGES = """
            module lib.c exposing ( Stage, Opening, Closing )
            data Opening
            data Closing
            data Stage = Opening | Closing
            """;

    private static final String B_OVER_OPENING = """
            module lib.b exposing ( Phase, inc )
            import lib.c ( Opening )
            data Phase = Opening
            behavior inc : (n: Int) -> Int
            let inc (n) = n + 1
            """;

    private static ReadableModule readBack(String module, Map<String, ClassFileImage> classes) {
        return assertInstanceOf(ReadableModule.class, assertInstanceOf(Readback.Ready.class,
                ModuleReadback.read(module, ModulePath.of(classes).declarations(),
                        DefaultStdlib.get().names())).value());
    }
}
