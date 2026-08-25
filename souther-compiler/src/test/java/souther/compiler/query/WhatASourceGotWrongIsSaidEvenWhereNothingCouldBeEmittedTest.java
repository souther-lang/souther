package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.source.SourceId;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a source got wrong is said whether or not anything could be run against it.
 *
 * <p>A file attached to a module may declare a name the module already declares, and its rows would
 * then read the other declaration — so the one written there says nothing, and that is reported
 * against the file it is written in. Whether this compile could emit classes for the module has
 * nothing to do with it: the clash is in the text.
 *
 * <p>It used to have everything to do with it. The classes were asked for first, and where there
 * were none the key answered with that and never got as far as reading what the file declared. A
 * module the JVM will not hold is exactly a module whose author still wants to be told what they
 * wrote twice.
 */
class WhatASourceGotWrongIsSaidEvenWhereNothingCouldBeEmittedTest {

    /** A module the language accepts and the JVM will not hold: a record wider than the slots a
     *  constructor has. It checks; nothing is emitted for it. */
    private static String tooWideForTheJvm() {
        List<String> fields = new ArrayList<>();
        for (int i = 0; i < 140; i++) {
            fields.add("f" + i + ": Int");
        }
        return """
            module example.wide

            data MemberId = String
            data Found = { id: MemberId }
            data Missing = { why: String }
            data Wide = { %s }

            behavior findMember : (id: MemberId) -> Found | Missing

            behavior place : (id: MemberId) -> Found | Missing
                depends on findMember

            let place (id, findMember) = findMember(id)
            let shared = MemberId("m-1")
            """.formatted(String.join(", ", fields));
    }

    /** A file attached to it that declares `shared` over again. */
    private static final String DECLARES_IT_AGAIN = """
            examples for example.wide

            let shared = MemberId("m-2")

            example place
                | "found" : (MemberId("m-1")) -> Found { id = MemberId("m-1") }
            """;

    private static final SourceId ATTACHED = new SourceId("1");

    @Test
    void aNameDeclaredTwiceIsSaidEvenWhereTheModuleCouldNotBeEmitted() {
        Db db = Compilation.ofSources(List.of(tooWideForTheJvm(), DECLARES_IT_AGAIN),
                ModulePath.EMPTY).db();

        Answer<Output.Examples.Of> answered =
                db.ask(Output.Examples.asked(db, "example.wide", ATTACHED));

        assertEquals(1, answered.reports().size(),
                () -> "the file declares a name the module declares: " + answered.reports());
        assertEquals("shared", answered.reports().get(0).diagnostic().values().get("name"),
                "and it is that name the report is about");
    }

    /**
     * And the module is one that checked, so the reading above is of a real state.
     *
     * <p>A module that failed earlier would report the clash for a reason that has nothing to do
     * with what this fixes.
     */
    @Test
    void andTheModuleItIsSaidOfIsOneThatChecked() {
        Db db = Compilation.ofSources(List.of(tooWideForTheJvm(), DECLARES_IT_AGAIN),
                ModulePath.EMPTY).db();

        assertTrue(db.ask(new Bodies.Checked("example.wide")).present(),
                "the language accepts it; it is the JVM that will not hold it");
        assertNotNull(ExampleExecutions.of(db, "example.wide"),
                "so its examples have an environment, and the clash is not read out of its absence");
    }

    /**
     * And what makes that environment is answered together.
     *
     * <p>{@link ExampleExecutions} takes a module's requirements and its contracts as conditions of
     * being ready, where one reader used to take a missing table as an empty one. That is a
     * condition tightened, and it holds because a module that checked has both — asserted here
     * rather than assumed, since it is what the tightening rests on.
     */
    @Test
    void andAModuleThatCheckedHasWhatAnEvaluationReads() {
        Db db = Compilation.ofSources(List.of(tooWideForTheJvm(), DECLARES_IT_AGAIN),
                ModulePath.EMPTY).db();

        assertNotNull(db.ask(new Bodies.Requirements("example.wide")).value(),
                "a module that checked knows what its behaviors need supplied");
        assertNotNull(db.ask(new Bodies.Contracts("example.wide")).value(),
                "and what they declare of what they answer");
    }
}
