package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.meta.ModulePath;
import souther.compiler.observe.ArmObservation;
import souther.compiler.observe.Incompleteness;
import souther.compiler.source.SourceId;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What went unbuilt is asked of the tables, not of the machine.
 *
 * <p>A source that states no table it builds built all none of them. Read the other way round — is
 * there a program to build against — a file that wrote no {@code fake} at all answers that its
 * tables could not be built, and the caller reads that as the file not having been answered for.
 * What that costs is the file's rows: a module the JVM will not hold still says which of its rows
 * could not be measured, and that would be thrown away by the answer to a question about fakes it
 * never wrote.
 *
 * <p>Which tables a source is the one to build is not "did it write one". A module's fakes are read
 * in one order and the first table for a dependency is the one that answers, so a file writing the
 * second one for a dependency states a table and builds none. The two readings are one answer
 * ({@code ExampleStatements.tablesBuiltIn}) so that they cannot come apart.
 */
class WhatWentUnbuiltIsAskedOfTheTablesAndNotOfTheMachineTest {

    /** A module the language accepts and the JVM will not hold, so nothing is emitted for it. */
    private static String tooWideForTheJvm(String ownFake) {
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
            %s
            """.formatted(String.join(", ", fields), ownFake);
    }

    private static final String A_FAKE = """
            fake findMember
                | (MemberId("m-1")) -> Missing { why = "no such member" }
            """;

    private static final SourceId ATTACHED = new SourceId("1");

    /** An attached file with a row and no fake at all. */
    private static final String A_ROW_AND_NO_FAKE = """
            examples for example.wide

            example place
                | "found" : (MemberId("m-1")) -> Missing { why = "no such member" }
            """;

    /** An attached file whose only fake is a second one for a dependency the module already
     *  answers for. It states a table and is not the one that builds it. */
    private static final String A_SECOND_FAKE_FOR_THE_SAME_DEPENDENCY = """
            examples for example.wide

            fake findMember
                | (MemberId("m-2")) -> Missing { why = "nor this one" }

            example place
                | "found" : (MemberId("m-1")) -> Missing { why = "no such member" }
            """;

    @Test
    void aSourceThatWroteNoFakeIsStillAnsweredForWhereNothingCouldBeEmitted() {
        Db db = Compilation.ofSources(List.of(tooWideForTheJvm(""), A_ROW_AND_NO_FAKE),
                ModulePath.EMPTY).db();

        Answer<Output.Examples.Of> answered = db.ask(
                new Output.Examples("example.wide", ATTACHED, ArmObservation.RECORD));

        assertNotNull(answered.value(),
                "it wrote no table, so nothing of its went unbuilt, and its rows still have"
                        + " something to say");
        assertEquals(List.of(Incompleteness.Code.INSTRUMENTATION_ABSENT),
                answered.value().incompleteness().stream().map(Incompleteness::code).toList(),
                "and what it says is that nothing recorded what its rows went through");
    }

    /**
     * And a file whose only fake is a second one for the same dependency is answered for too.
     *
     * <p>It wrote a fake, so a rule that asked whether the file wrote one would call its tables
     * unbuilt — and the file is not the one that builds it either way.
     */
    @Test
    void aSourceWhoseOnlyFakeAnswersNothingIsAnsweredForToo() {
        Db db = Compilation.ofSources(
                List.of(tooWideForTheJvm(A_FAKE), A_SECOND_FAKE_FOR_THE_SAME_DEPENDENCY),
                ModulePath.EMPTY).db();

        Answer<Output.Examples.Of> answered = db.ask(
                new Output.Examples("example.wide", ATTACHED, ArmObservation.RECORD));

        assertNotNull(answered.value(),
                "the module answers for that dependency, so this file builds no table of its own");
    }

    /** And the module really is one that checks and emits nothing, so the two above are read of the
     *  state they are written for. */
    @Test
    void andTheModuleItSaysThisOfChecksAndEmitsNothing() {
        Db db = Compilation.ofSources(List.of(tooWideForTheJvm(""), A_ROW_AND_NO_FAKE),
                ModulePath.EMPTY).db();

        assertTrue(db.ask(new Bodies.Checked("example.wide")).present(),
                "the language accepts it");
        assertTrue(db.ask(new Output.EvaluationLinked("example.wide",
                ArmObservation.OMIT)).value() == null, "and the JVM will not hold it");
    }
}
