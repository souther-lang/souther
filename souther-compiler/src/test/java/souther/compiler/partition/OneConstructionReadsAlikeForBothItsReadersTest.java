package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.Compiler;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The check that discharges a clause and the measure that finds a line read one construction alike.
 *
 * <p>Two readers walk one grammar with leaves of their own, and what each of them keeps in its leaf
 * is what the other is free not to have. A newtype's construction was a number to the check and an
 * expression nobody could read to the measure, so a threshold this compiler was willing to reason
 * with was reported as one it could not read — one model, measured against two accounts of what a
 * construction is.
 *
 * <p>Held on one source rather than two. The claim is not that both readers are correct about their
 * own fixture; it is that the same four lines say the same thing to both of them, which two
 * fixtures written apart cannot say however carefully they are kept alike.
 *
 * <p>What owns the reading is held elsewhere and separately
 * ({@code WhatThisGrammarReadsIsReadWithoutACallersLeafTest}): this pair would go on passing if the
 * rule were copied into both leaves, which is the shape it is here to keep from coming back.
 */
class OneConstructionReadsAlikeForBothItsReadersTest {

    private static final String MODULE = """
            module demo

            data Yen = Int
            data Big = { threshold: Int }
            data Amount = Int
                invariant atLeastAHundred = value >= 100

            behavior throughARecord : (n: Int) -> Amount
                constructs Amount, Big
            let throughARecord (n) =
                if n >= Big { threshold = 99 + 1 }.threshold then Amount(n) else Amount(100)

            behavior throughANewtype : (n: Int) -> Amount
                constructs Amount, Yen
            let throughANewtype (n) =
                if n >= Yen(99 + 1).value then Amount(n) else Amount(100)

            example throughARecord
                | "under" : (1) -> Amount(100)

            example throughANewtype
                | "under" : (1) -> Amount(100)
            """;

    /**
     * The check has what it needs to discharge the invariant on the side the rule keeps.
     *
     * <p>{@code Amount(n)} stands where {@code n} is at least a hundred, and the only thing that
     * says so is the comparison beside it having been read. A reader that stopped at the
     * construction knows nothing there and says so.
     */
    @Test
    void theCheckReadsTheThresholdItWasComparedAgainst() {
        assertEquals(List.of(), Compiler.compileWithWarnings(MODULE).warnings().stream()
                .map(each -> each.code() + " " + each.primary()).toList());
    }

    /** And the measure draws the line the same comparison states, at the same number. */
    @Test
    void theMeasureDrawsTheLineTheSameComparisonStates() {
        Compilation compilation = Compilation.ofSource(MODULE, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        assertEquals(Map.of("throughARecord", "n/x < 100, n/100 <= x",
                        "throughANewtype", "n/x < 100, n/100 <= x"),
                AdequacyReport.of(compilation).modules().get(0).behaviors().stream()
                        .collect(Collectors.toMap(AdequacyReport.BehaviorReport::name,
                                behavior -> behavior.partition().axes().stream()
                                        .flatMap(axis -> axis.classes().stream())
                                        .collect(Collectors.joining(", ")))));
    }
}
