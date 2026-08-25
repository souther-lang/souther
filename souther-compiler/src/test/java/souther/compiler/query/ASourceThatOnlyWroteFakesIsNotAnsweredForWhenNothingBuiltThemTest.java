package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.source.SourceId;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A source whose fakes were never built is not a source whose fakes are fine.
 *
 * <p>The two were one answer. Building the table a {@code fake} states runs what the compile
 * generated, so a module with no classes builds none of them — and what came back was the empty
 * list a build that found nothing wrong comes back with. A file that writes only fakes has no rows
 * either, so the whole answer for it was "no observations, nothing wrong" about a file nothing had
 * read.
 *
 * <p>Which is not an edge of the language, in either half. A file is attached to a module for its
 * rows <em>or</em> its fakes, and one that writes only fakes is an ordinary way to write them. And a
 * module that checks and cannot be emitted is what this whole boundary is about: the JVM will not
 * hold a declaration this wide, and the language has nothing against it.
 */
class ASourceThatOnlyWroteFakesIsNotAnsweredForWhenNothingBuiltThemTest {

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
            """.formatted(String.join(", ", fields));
    }

    /** The same module, narrow enough to emit. */
    private static String heldByTheJvm() {
        return tooWideForTheJvm().replaceAll("data Wide = \\{[^}]*\\}", "data Wide = { f0: Int }");
    }

    /** A file attached to it that writes a fake and no rows. */
    private static final String ONLY_A_FAKE = """
            examples for example.wide

            fake findMember
                | (MemberId("m-1")) -> Missing { why = "no such member" }
            """;

    private static final SourceId ATTACHED = new SourceId("1");

    @Test
    void aSourceWhoseFakesCouldNotBeBuiltIsNotAnsweredFor() {
        Db db = Compilation.ofSources(List.of(tooWideForTheJvm(), ONLY_A_FAKE),
                ModulePath.EMPTY).db();

        Answer<Output.Examples.Of> answered =
                db.ask(Output.Examples.asked(db, "example.wide", ATTACHED));

        assertNull(answered.value(),
                "nothing built the fakes this file wrote, so nothing here answers for it");
    }

    /**
     * And it is the emitting that this turns on, not the module being unreadable.
     *
     * <p>The module checks either way. Without this, the rule above would hold of a module that
     * failed something earlier, and would say nothing about the state it was written for.
     */
    @Test
    void andTheModuleItSaysThisOfIsOneThatChecked() {
        Db db = Compilation.ofSources(List.of(tooWideForTheJvm(), ONLY_A_FAKE),
                ModulePath.EMPTY).db();

        assertTrue(db.ask(new Bodies.Checked("example.wide")).present(),
                "the language accepts it; it is the JVM that will not hold it");
        assertNotNull(ExampleExecutions.of(db, "example.wide"),
                "and its examples have everything they need to be evaluated");
        assertFalse(db.ask(new Output.EvaluationLinked("example.wide",
                        souther.compiler.observe.ArmObservation.OMIT)).present(),
                "what it has not got is classes");
    }

    /**
     * And the same file is answered for where the tables can be built.
     *
     * <p>Otherwise the rule would be "a file that writes only fakes is never answered for", which
     * passes the same way and says nothing.
     */
    @Test
    void andItIsAnsweredForWhereTheyCanBe() {
        Db db = Compilation.ofSources(List.of(heldByTheJvm(), ONLY_A_FAKE), ModulePath.EMPTY).db();

        Answer<Output.Examples.Of> answered =
                db.ask(Output.Examples.asked(db, "example.wide", ATTACHED));

        assertNotNull(answered.value(),
                "the fakes build here, so the file is answered for — with no rows in it");
    }
}
