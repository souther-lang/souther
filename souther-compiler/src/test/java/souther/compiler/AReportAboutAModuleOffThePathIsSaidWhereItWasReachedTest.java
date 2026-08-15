package souther.compiler;

import souther.compiler.diag.Citation;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Region;
import souther.compiler.diag.msg.ModuleMessage;
import souther.compiler.diag.msg.NameMessage;
import souther.compiler.diag.Located;
import souther.compiler.diag.SourcePos;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A module read off the class path is read from text this compile put back together out of what the
 * module published, so a coordinate in it is a line and a column of a file nobody holds. A report
 * found there is said at the nearest place on the way to that module a source of this compilation
 * writes, and names where the code is rather than pointing at it.
 *
 * <p>Both halves matter. Quoted as it stands, the coordinate lands wherever those numbers happen to
 * fall in the file the author is looking at — a compile of one source has no way to tell an untagged
 * report from one about no file at all — and filed as it stands it lands nowhere, which left a
 * failing compile answering no classes and no diagnostics.
 */
class AReportAboutAModuleOffThePathIsSaidWhereItWasReachedTest {

    /** A module compiled against {@code path}, as its own project's build produced it. */
    private static Map<String, byte[]> built(String source, Map<String, byte[]> path) {
        return Compiler.compileModules(List.of(source), path::get);
    }

    private static Map<String, byte[]> and(Map<String, byte[]> one, Map<String, byte[]> other) {
        Map<String, byte[]> both = new java.util.LinkedHashMap<>(one);
        both.putAll(other);
        return both;
    }

    private static Compilation reading(String source, Map<String, byte[]> path) {
        Compilation compilation = Compilation.ofSources(List.of(source), path::get);
        compilation.answerEverything();
        return compilation;
    }

    /** A module holding one thing out of another, as its own project's build produced it. */
    private static Map<String, byte[]> holding(String name, String type, String from,
                                               String imported, Map<String, byte[]> path) {
        return built("""
                module %s exposing ( %s )
                import %s ( %s )

                data %s = { x: %s }
                """.formatted(name, type, from, imported, type, imported), path);
    }

    /** The classes of {@code lib.deep}, which every path here leaves out. */
    private static Map<String, byte[]> deep() {
        return Compiler.compile("""
                module lib.deep exposing ( Deep )
                data Deep = String
                """);
    }

    /** The declaring project's build of {@code lib.held}, which needs {@code lib.deep}. */
    private static Map<String, byte[]> held() {
        return built("""
                module lib.held exposing ( Held )
                import lib.deep ( Deep )

                data Held = { deep: Deep }
                """, deep());
    }

    @Test
    void itIsSaidAtTheImportThatNamedTheModule() {
        // `lib.held` is on the path and the module it needs is not, so reading it back has something
        // to report about a declaration written where this compile has no file.
        Compilation compilation = reading("""
                module app.uses




                import lib.held ( Held )

                data Page = { held: Held }
                """, held());

        SourcePos said = whereTheReportAboutIsSaid(compilation, "lib.held");
        assertEquals("0", said.sourceId(), "a reader can only be sent to a file this compile holds");
        assertEquals(6, said.line(), "the import line naming the module, not a line of the module");
        assertEquals(1, said.column());
    }

    /** The coordinate says the code is elsewhere, so no surface reads it as the place. */
    @Test
    void theCoordinateStandsInForCodeWrittenInThatModule() {
        Compilation compilation = reading("""
                module app.uses
                import lib.held ( Held )

                data Page = { held: Held }
                """, held());

        Citation citation = Citation.of(whereTheReportAboutIsSaid(compilation, "lib.held"));

        assertEquals("lib.held",
                assertInstanceOf(Citation.OutOfSight.class, citation).declaration());
    }

    /**
     * A module reached only through another off the path inherits that one's place. There is no
     * import line naming it anywhere a reader here can look, and the one naming the dependency that
     * led there is the nearest thing there is.
     */
    @Test
    void oneReachedThroughAnotherIsSaidAtTheImportThatLedThere() {
        Map<String, byte[]> held = held();
        Map<String, byte[]> front = built("""
                module lib.front exposing ( Front )
                import lib.held ( Held )

                data Front = { held: Held }
                """, and(held, deep()));

        Compilation compilation = reading("""
                module app.uses


                import lib.front ( Front )

                data Page = { front: Front }
                """, and(held, front));

        SourcePos said = whereTheReportAboutIsSaid(compilation, "lib.held");
        assertEquals("0", said.sourceId());
        assertEquals(4, said.line(), "the import of the dependency that led to it");
    }

    /** The route this was found on. The report is about a module the caller has no file for, and it
     *  still reaches the file the caller does have. */
    @Test
    void itIsPublishedOnTheSourceThatReachedIt() {
        Compilation compilation = reading("""
                module app.uses
                import lib.held ( Held )

                data Page = { held: Held }
                """, held());

        List<Located> onTheSource = compilation.diagnostics().get("0");
        assertNotNull(onTheSource);
        assertFalse(onTheSource.isEmpty(),
                "a compile that emitted nothing said nothing about why");
    }

    /**
     * Every error reaches a file. What the command line stops for and what an editor marks are the
     * same set, and a report that reached neither is one the author is never told about — the
     * walk over the path is one question about the whole compilation and names no module of its
     * own, so what it finds has to say where it is said.
     *
     * <p>Measured on the reports rather than on the classes. A compile that emits nothing and says
     * nothing is what this looked like, but which of those is the defect is the second one: what a
     * build produces is its own question, and one that legitimately produces no classes would make
     * the first reading say this had been fixed.
     */
    @Test
    void noErrorIsLeftWithNowhereToBeSaid() {
        Compilation compilation = reading("""
                module app.uses
                import lib.held ( Held )

                data Page = { held: Held }
                """, held());

        List<String> unreachable = new ArrayList<>();
        for (Db.Found found : compilation.reports()) {
            if (found.report().isError() && compilation.publishSourceIdsOf(found).isEmpty()) {
                unreachable.add(found.report().diagnostic().code() + " about " + found.module());
            }
        }
        assertEquals(List.of(), unreachable, "an error the author is never shown");
    }

    /**
     * A dependency two files import is reached by both, and both authors are told.
     *
     * <p>Neither import is the premise the other is measured by, and neither author has anything
     * different to do about it. Marking one of them leaves the other looking at a file that is fine
     * while the build fails — and which of the two it would be is the order the sources happened to
     * arrive in.
     */
    @Test
    void everySourceThatReachesItIsTold() {
        Compilation compilation = Compilation.ofSources(List.of("""
                module app.a exposing ( A )
                import lib.held ( Held )

                data A = { held: Held }
                """, """
                module app.b exposing ( B )
                import lib.held ( Held )

                data B = { held: Held }
                """), held()::get);
        compilation.answerEverything();

        Map<String, List<Located>> byId = compilation.diagnostics();
        assertFalse(byId.get("0").isEmpty(), "the source that was reached first");
        assertFalse(byId.get("1").isEmpty(), "the one that reaches it just as much");
    }

    /**
     * A route found after the module it leads to was read counts as much as the one found before.
     *
     * <p>The walk reads each module once, and a place written down when it was read is the places it
     * had by then. Here one source names the shared dependency outright and the other reaches it
     * through a dependency of its own, so the second route arrives after the shared module has been
     * read and everything under it settled — and the author of the second file was told nothing
     * about a missing dependency their import reaches. Which file that is comes down to nothing
     * either author wrote.
     */
    @Test
    void aRouteFoundAfterTheModuleWasReadCountsToo() {
        Map<String, byte[]> shared = built("""
                module lib.shared exposing ( Shared )
                import lib.deep ( Deep )

                data Shared = { deep: Deep }
                """, deep());
        Map<String, byte[]> between = built("""
                module lib.between exposing ( Between )
                import lib.shared ( Shared )

                data Between = { shared: Shared }
                """, and(shared, deep()));

        Compilation compilation = Compilation.ofSources(List.of("""
                module app.a exposing ( A )
                import lib.shared ( Shared )

                data A = { shared: Shared }
                """, """
                module app.b exposing ( B )
                import lib.between ( Between )

                data B = { between: Between }
                """), and(shared, between)::get);
        compilation.answerEverything();

        Map<String, List<Located>> byId = compilation.diagnostics();
        assertEquals(byId.get("0").size(), byId.get("1").size(),
                "the file that reaches it the long way round is told the same things");
    }

    /**
     * Two routes of different lengths meeting at one module carry both origins on down.
     *
     * <p>{@code app.a} reaches the meeting point through one module and {@code app.b} through two,
     * so the meeting point is read while only the short route is known and everything under it is
     * settled from that. What the long route adds arrives afterwards and has to travel the rest of
     * the way — reaching a module is reaching everything it reaches, and where the two routes happen
     * to be the same length is not what decides it.
     */
    @Test
    void routesOfDifferentLengthsBothReachWhatTheyMeetOver() {
        Map<String, byte[]> leaf = Compiler.compile("""
                module lib.leaf exposing ( Leaf )
                data Leaf = String
                """);
        Map<String, byte[]> meeting = holding("lib.meeting", "Meeting", "lib.leaf", "Leaf", leaf);
        Map<String, byte[]> shortWay = holding("lib.short", "Short", "lib.meeting", "Meeting",
                and(meeting, leaf));
        Map<String, byte[]> middle = holding("lib.middle", "Middle", "lib.meeting", "Meeting",
                and(meeting, leaf));
        Map<String, byte[]> longWay = holding("lib.long", "Long", "lib.middle", "Middle",
                and(middle, and(meeting, leaf)));

        // everything but the leaf, so what is missing is under the module the two routes meet at
        Compilation compilation = Compilation.ofSources(List.of("""
                module app.a exposing ( A )
                import lib.short ( Short )

                data A = { x: Short }
                """, """
                module app.b exposing ( B )
                import lib.long ( Long )

                data B = { x: Long }
                """), and(and(meeting, shortWay), and(middle, longWay))::get);
        compilation.answerEverything();

        Map<String, List<Located>> byId = compilation.diagnostics();
        assertEquals(byId.get("0").size(), byId.get("1").size(),
                "the file that reaches the meeting point the long way round is told the same things");
    }

    /**
     * Two modules each needing the same absent one are two things to be told.
     *
     * <p>They are missing from two places. An author who reaches one of them has not reached the
     * other, so one report pointing at both imports would say the code is written in a module that
     * import never arrives at — a statement about a place, and false. What is absent is the edge and
     * not the module.
     */
    @Test
    void twoModulesNeedingTheSameAbsentOneAreTwoFindings() {
        Map<String, byte[]> left = holding("lib.left", "Left", "lib.deep", "Deep", deep());
        Map<String, byte[]> right = holding("lib.right", "Right", "lib.deep", "Deep", deep());

        Compilation compilation = Compilation.ofSources(List.of("""
                module app.a exposing ( A )
                import lib.left ( Left )

                data A = { x: Left }
                """, """
                module app.b exposing ( B )
                import lib.right ( Right )

                data B = { x: Right }
                """), and(left, right)::get);
        compilation.answerEverything();

        Set<String> saidAbout = new LinkedHashSet<>();
        for (Db.Found found : compilation.reports()) {
            SourcePos at = found.report().diagnostic().pos();
            if (at == null || !at.isOutOfSight()) {
                continue;
            }
            String stands = ((Citation.OutOfSight) Citation.of(at)).declaration();
            saidAbout.add(stands);
            // Every file it is said in, and not only the one the caret is in: a second place is
            // said as a labelled region, and claiming a file that never reaches this module is
            // exactly what putting both imports on one report would do.
            assertEquals(List.of("lib.left".equals(stands) ? "0" : "1"),
                    compilation.publishSourceIdsOf(found),
                    "`" + stands + "` is not reached from the other file at all");
        }
        assertEquals(Set.of("lib.left", "lib.right"), saidAbout,
                "each of them needs it, and each of them is a thing to be told");
    }

    /**
     * A module on the path that took a name no module may take is refused, and the refusal is said
     * where the module was reached from.
     *
     * <p>The other thing this walk finds on its own. It is refused rather than read, so it has no
     * declarations for anything else to trip over and nothing later says it again — which is what
     * left it as the one report here still carrying a coordinate in a file nobody holds.
     */
    @Test
    void aModuleOnThePathThatTookAReservedNameIsRefusedWhereItWasReached() {
        Compilation core = Compilation.ofCoreSource("""
                module souther.taken exposing ( X )
                data X = Int
                """);
        core.answerEverything();

        Compilation compilation = reading("""
                module app.uses
                import souther.taken ( X )

                data A = { x: X }
                """, core.classes());

        List<Located> onTheSource = compilation.diagnostics().get("0");
        assertNotNull(onTheSource);
        // That one, and only that one. A module the path holds and this compilation refuses is
        // still a module it has heard of, so an importer of it is not also told there is no such
        // thing — two reports that cannot both be true.
        assertEquals(List.of("E1502"),
                onTheSource.stream().map(said -> said.diagnostic().code()).toList());
    }

    /**
     * Two findings that differed only in where they were written are said once.
     *
     * <p>Reading a report for where it may be said is what makes them one. Their coordinates are in
     * a text nobody holds and are what told them apart; said at the place the module was reached
     * from, they are one sentence at one caret, and an author shown it twice has nothing to tell
     * them apart by either.
     */
    @Test
    void twoFindingsInOnePublishedModuleAreSaidOnce() {
        Map<String, byte[]> withDeep = Compiler.compile("""
                module lib.deep exposing ( Deep )
                data Deep = String
                """);
        Map<String, byte[]> twice = built("""
                module lib.twice exposing ( Twice )
                data Twice = { a: lib.deep.Deep, b: lib.deep.Deep }
                """, withDeep);
        // the dependency is rebuilt without the type, so both field types fail to resolve
        Map<String, byte[]> withoutDeep = Compiler.compile("""
                module lib.deep exposing ( Other )
                data Other = String
                """);

        Compilation compilation = reading("""
                module app.uses
                import lib.twice ( Twice )

                data Page = { twice: Twice }
                """, and(withoutDeep, twice));

        assertEquals(2, compilation.db().allReports().size(),
                "two findings, at the two places the module writes the name");
        assertEquals(1, compilation.diagnostics().get("0").size(),
                "one thing to be told, said once");
    }

    /**
     * A report whose caret stays put keeps every label it had.
     *
     * <p>A label naming no source of its own is read in the diagnostic's, which is what a hand-made
     * position is for and is a contract older than any of this. Only moving the caret takes that
     * away — the file the label would be read in stops being the file it was built against — so a
     * reading that dropped such a label from every report would be reading "no file of its own" as
     * "no file at all", which is a different thing and is already answered.
     */
    @Test
    void anOrdinaryReportKeepsALabelThatNamesNoSourceOfItsOwn() {
        Diagnostic said = Diagnostic.say(new NameMessage.NoValueOfThatNameInScope("x"))
                .at(new SourcePos(1, 1, "0"))
                .secondary(Region.ofWidth(new SourcePos(3, 3), 4),
                        new NameMessage.WriteItOnItsOwn("x"))
                .build();

        assertEquals(1, said.secondary().size(), "the label is there to begin with");
        assertEquals("0", said.secondary().get(0).sourceIdOr("0"),
                "and is read in the file the diagnostic is in");

        Diagnostic moved = said.reachedFrom(List.of(new SourcePos(2, 1, "0")), "lib.held",
                new ModuleMessage.ItIsReachedFromHereToo());

        assertEquals(List.of(), moved.secondary(),
                "moving the caret is what takes the label's file away");
    }

    /** Where the report about {@code module} is said. */
    private static SourcePos whereTheReportAboutIsSaid(Compilation compilation, String module) {
        List<SourcePos> said = new ArrayList<>();
        for (Db.Found found : compilation.reports()) {
            if (module.equals(found.module()) && found.report().diagnostic().pos() != null) {
                said.add(found.report().diagnostic().pos());
            }
        }
        assertFalse(said.isEmpty(), "nothing was reported about " + module);
        return said.get(0);
    }
}
