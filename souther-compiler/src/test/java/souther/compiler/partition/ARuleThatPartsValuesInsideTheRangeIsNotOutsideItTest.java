package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A rule parting values the quantity holds is not a rule whose line the quantity never reaches.
 *
 * <p>Whether a quantity runs as far as a rule's line is asked before anything else about that line,
 * and a rule that draws nowhere has to be said to draw nowhere rather than joining an arrangement.
 * What it is asked of is where the rule parts the values, which on a carrier that counts is one
 * count in from the number the rule wrote — so a rule refusing its own threshold parts the values
 * one step inside the range the same rules leave, and asked at the threshold it comes back as a
 * rule cutting outside them.
 *
 * <p>Which is a sentence about the model and not about this compiler: a reader told the quantity
 * never reaches the line goes looking for a bound that is not there, over a rule that parts values
 * the model holds.
 *
 * <p>Read against the operator one character away, because that is the whole difference. The two
 * write one number and part the values one count apart, and only one of them is a step inside the
 * range.
 */
class ARuleThatPartsValuesInsideTheRangeIsNotOutsideItTest {

    private static final String MODULE = "example.strict";

    private static String model(String clause) {
        return """
                module example.strict

                data Ok

                data Span = { lo: Int, hi: Int }
                    %s

                behavior read : (s: Span) -> Int
                let read (s) = s.hi

                example read | "x" : (Span { lo = 1, hi = 3 }) -> 3
                """.formatted(clause);
    }

    /** Every line this behavior's positions are held to, wherever it was drawn. */
    private static List<Border> lines(String clause) {
        Compilation compilation = Compilation.ofSource(model(clause), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Partitions.Partitioning divided =
                compilation.db().ask(new Adequacy.Divided(MODULE, "read")).value();
        assertNotNull(divided, "the model under test compiles and is measured");
        List<Border> out = new java.util.ArrayList<>(divided.between());
        divided.along().values().forEach(out::addAll);
        return out;
    }

    /** The control: the rule that admits its own threshold draws its line. */
    @Test
    void aRelationAdmittingItsThresholdDrawsItsLine() {
        assertEquals(1, lines("invariant lo <= hi").size(),
                () -> "the pair parts where the two are level: " + lines("invariant lo <= hi"));
    }

    /**
     * And so does the one that refuses it, which parts the values one count in.
     *
     * <p>The same rule one character away. It parts the whole numbers between minus one and zero,
     * and the range the same rule leaves stops at minus one — so the line is a step inside what the
     * quantity holds and not beyond it.
     */
    @Test
    void aRelationRefusingItsThresholdDrawsItsLineToo() {
        assertEquals(1, lines("invariant lo < hi").size(),
                () -> "the pair parts one count in from level: " + lines("invariant lo < hi"));
    }

    /**
     * And a rule whose line the quantity really never reaches still draws none.
     *
     * <p>The negative control, and the reason the question is asked at all. A length is never
     * negative, so a rule bounding one below zero parts nothing: there is no value either side of
     * its line for a row to be owed at, and a reading that answered every rule alike would offer
     * rows against it.
     */
    @Test
    void aRuleCuttingWhereTheQuantityNeverRunsStillDrawsNothing() {
        String model = """
                module example.strict

                data Ok

                data Bag = { xs: List<Int> }
                    invariant List.length(xs) <= 0 - 1

                behavior read : (b: Bag) -> Int
                let read (b) = List.length(b.xs)

                example read | "x" : (Bag { xs = [1] }) -> 1
                """;
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Partitions.Partitioning divided =
                compilation.db().ask(new Adequacy.Divided(MODULE, "read")).value();
        assertNotNull(divided, "the model under test compiles and is measured");

        assertEquals(List.of(), divided.between(),
                "nothing the rules leave is either side of that line");
    }
}
