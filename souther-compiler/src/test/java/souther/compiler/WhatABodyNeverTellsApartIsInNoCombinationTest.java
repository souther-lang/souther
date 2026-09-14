package souther.compiler;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A position the model divides and the body never tells apart is in no combination.
 *
 * <p>Divided is not the same as worth combining. A sum divides a position by being a sum, and a
 * behavior that takes it and never looks at it answers the same however it moves — so a row at a
 * combination of it with something else shows nothing the two rows apart do not, and nothing is
 * owed there. What the position keeps is the rows its own classes are owed.
 *
 * <p>Which is the fallback holding to what ADR-0108 decided for the generation: the body is here,
 * and the product of every two positions is what a measure with the body out of view has to assume.
 * A behavior whose decisions meet nowhere falls back to the pair space and not to that assumption.
 */
class WhatABodyNeverTellsApartIsInNoCombinationTest {

    /** `kind` is a sum the body never looks at; `cost` is what the guard decides on. */
    private static final String MODEL = """
            module example.untold

            data Domestic
            data Overseas
            data Kind = Domestic | Overseas
            data Amount = Int
                invariant value >= 0
            data Submitted = { cost: Amount }
            data Waiting = { cost: Amount }

            behavior submit : (kind: Kind, cost: Amount) -> Submitted | Waiting
                constructs Submitted, Waiting

            let submit (kind, cost) = {
                guard cost.value <= 100 else Waiting { cost = cost }
                Submitted { cost = cost }
            }

            example submit
                | (Overseas, Amount(0))   -> Submitted { cost = Amount(0) }
                | (Domestic, Amount(101)) -> Waiting { cost = Amount(101) }
            """;

    /**
     * Both positions are divided, one of them is in the space, and so there is no relation.
     *
     * <p>The classes measure still holds `kind` to its own two classes: what goes is the product
     * of it with the position the body does decide on.
     */
    @Test
    void thePositionTheBodyNeverLooksAtIsInNoRelation() {
        PartitionEvidence partition = measured();

        assertEquals(2, partition.axes().size(), "the model divides both positions");
        assertTrue(partition.axes().stream().allMatch(each -> each.classes().size() >= 2),
                "and each into classes");
        assertEquals(List.of(), partition.pairs().space(),
                "the space is over what the body tells apart, which is one position");
    }

    /** So nothing is owed at a combination, and the report says nothing about one. */
    @Test
    void andNothingIsOwedAtACombinationOfIt() {
        Compilation compilation = compiled();
        List<Adequacy.Finding> findings =
                compilation.db().ask(new Adequacy.Findings("example.untold")).value();

        assertTrue(findings.stream().noneMatch(each -> each.kind() == Adequacy.Kind.PAIR_UNCOVERED),
                () -> "a combination of a position the body never looks at: " + findings);
        assertFalse(souther.compiler.report.AdequacyReport.of(compilation)
                        .human(souther.compiler.diag.SourceRendering
                                .namedByIdentity(compilation.texts()))
                        .contains("    combination "),
                "and no count of one is printed");
    }

    private static PartitionEvidence measured() {
        Map<String, PartitionEvidence> all = compiled().db()
                .ask(new Adequacy.Coverage("example.untold")).value();
        return all.get("submit");
    }

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
