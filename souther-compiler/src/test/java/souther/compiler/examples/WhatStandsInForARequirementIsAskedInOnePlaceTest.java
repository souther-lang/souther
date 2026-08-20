package souther.compiler.examples;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What stands in for a behavior's requirement while an example runs, and where that was found.
 *
 * <p>Two things may stand in — a {@code with} written on the row, and a {@code fake} table written
 * beside it — and the row is looked at first. That order, and the fact that there are two of them at
 * all, is what E1908 is about: a row whose target depends on something neither supplies cannot run,
 * and the message says both ways to answer it.
 *
 * <p>It lived inside the verifier, wound together with building the value each stand-in answers
 * with. A reader that only wants to know whether a requirement is still owed — an editor offering to
 * write a row, which cannot build a value because it has none yet — had nowhere to ask, and asking
 * by looking for a {@code with} and then a {@code fake} itself would be this rule written a second
 * time.
 *
 * <p>The answer carries what it found rather than a yes or no, because the two callers do different
 * things with it: one builds a stand-in out of it, the other counts what is left.
 */
class WhatStandsInForARequirementIsAskedInOnePlaceTest {

    private static final String FAKED = """
            module example.faked

            data MemberId = String
            data Found = { id: MemberId }
            data Missing = { why: String }

            behavior findMember : (id: MemberId) -> Found | Missing

            behavior place : (id: MemberId) -> Found | Missing
                depends on findMember

            let place (id, findMember) = findMember(id)

            fake findMember
                | _ -> Missing { why = "none" }

            example place
                | (MemberId("m-1")) -> Missing { why = "none" }
            """;

    private static final String WITH_ON_THE_ROW = """
            module example.withrow

            data MemberId = String
            data Found = { id: MemberId }
            data Missing = { why: String }

            behavior findMember : (id: MemberId) -> Found | Missing

            behavior place : (id: MemberId) -> Found | Missing
                depends on findMember

            let place (id, findMember) = findMember(id)

            fake findMember
                | _ -> Missing { why = "none" }

            example place
                | (MemberId("m-1")) with findMember = Found { id = MemberId("m-1") }
                    -> Found { id = MemberId("m-1") }
            """;

    /** A table beside the rows stands in where the row says nothing. */
    @Test
    void aTableStandsInWhereTheRowSaysNothing() {
        Model model = modelOf(FAKED);
        assertInstanceOf(ExampleProvisioning.Standin.InTheModule.class,
                ExampleProvisioning.standingIn(model.row().withs(), "findMember", model.execution()));
    }

    /** And the row is looked at first, so what it writes stands in over the table beside it. */
    @Test
    void theRowIsLookedAtBeforeTheTableBesideIt() {
        Model model = modelOf(WITH_ON_THE_ROW);
        ExampleProvisioning.Standin found =
                ExampleProvisioning.standingIn(model.row().withs(), "findMember", model.execution());
        assertInstanceOf(ExampleProvisioning.Standin.OnTheRow.class, found,
                "the `with` on the row was passed over for the table beside it");
    }

    /** Something neither supplies is owed, which is what E1908 is said about. */
    @Test
    void aRequirementNeitherSuppliesIsOwed() {
        Model model = modelOf(FAKED);
        assertInstanceOf(ExampleProvisioning.Standin.Nothing.class,
                ExampleProvisioning.standingIn(model.row().withs(), "somethingElse",
                        model.execution()));
    }

    /**
     * A row that is not written yet supplies nothing, and is asked the same question.
     *
     * <p>What a row contributes is its {@code with}s, so a row nobody has written contributes an
     * empty list rather than a stand-in row built to be asked with. Its target's requirements are
     * then owed exactly where nothing else answers them, which is what an editor has to know before
     * it can offer a row that will run.
     */
    @Test
    void aRowNotWrittenYetSuppliesNothingOfItsOwn() {
        Model model = modelOf(WITH_ON_THE_ROW);
        assertInstanceOf(ExampleProvisioning.Standin.InTheModule.class,
                ExampleProvisioning.standingIn(List.of(), "findMember", model.execution()),
                "the table beside the rows answers a row that has not been written");
        assertEquals(List.of(),
                ExampleProvisioning.unsupplied(List.of(), List.of("findMember"), model.execution()));
        assertEquals(List.of("somethingElse"),
                ExampleProvisioning.unsupplied(List.of(), List.of("findMember", "somethingElse"),
                        model.execution()));
    }

    private record Model(Hir.ExampleRow row, Prepared.ExampleExecution execution) {}

    private static Model modelOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        assertNotNull(prepared, "the model under test compiles");
        Hir.ExampleRow row = prepared.examples().get(0).read().rows().get(0);
        return new Model(row, prepared.forExamples());
    }
}
