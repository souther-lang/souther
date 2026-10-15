package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.DiagnosticCode;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeKey;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A product's meaning is made by reading its clauses, and a clause that walks declarations asks
 * each whether it is a sum by its form, not by what it says.
 *
 * <p>The product being made is among the declarations such a walk meets, and what it says is the
 * answer being made. Which form it is was settled when the module was indexed, so a walk that asks
 * that first, and what a declaration says only of the sums, never meets it.
 */
class WhatAProductSaysIsMadeWithoutAskingItWhatItSaysTest {

    /**
     * An arm naming a case of another sum is reported with the sum it is a case of, which is found
     * by going through every visible name. {@code Item} is one of them, and its clause is the one
     * being read.
     */
    @Test
    void anArmOfAnotherSumInAClauseIsReportedWithoutAskingTheProduct() {
        Compilation c = Compilation.ofDocuments(Map.of("shop.sou", """
                module shop

                data Red
                data Green
                data Colour = Red | Green

                data Item =
                    { colour: Colour
                    }
                    invariant fine = match colour with
                        | Red -> true
                        | Small -> false

                data Small
                data Large
                data Size = Small | Large
                """), Set.of(), ModulePath.EMPTY);

        assertTrue(c.db().ask(new Shapes.MeaningOf(new TypeKey("shop", "Item"))).present(),
                "what `Item` says is made before anything else is asked");
        c.answerEverything();
        assertEquals(List.of(DiagnosticCode.E1203.name()), c.db().allReports().stream()
                        .map(each -> each.report().diagnostic().code()).distinct().toList(),
                "the arm is reported as naming no case of `Colour`");
    }
}
