package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.partition.GenerationReason;
import souther.compiler.partition.Generator;
import souther.compiler.query.Adequacy;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a generation that held work back says to the author.
 *
 * <p>The sentence is the whole of why this reason exists. A combination passed over because a row
 * already written sits where a filling row would is one nothing established anything about, and
 * saying nothing about it reads as one that is covered. So the line is held to word for word:
 * printed with its parts in the wrong places it names a behavior where a count belongs and reads as
 * being about something else entirely, which is a sentence that says nothing and looks like it says
 * something.
 */
class WhatAGenerationHeldBackIsSaidInWordsTest {

    @Test
    void oneCombinationHeldBackNamesItsBehaviorAndSaysWhatIsUnknown() {
        assertTrue(said(new GenerationReason.CombinationsWithheld("shippingFee", 1)).contains(
                        "// 1 combination for `shippingFee` offered no row: one already written"
                                + " sits where a row filling it would, and nothing ran to say"
                                + " whether it does"),
                said(new GenerationReason.CombinationsWithheld("shippingFee", 1)));
    }

    @Test
    void severalAreCountedAsSeveral() {
        assertTrue(said(new GenerationReason.CombinationsWithheld("shippingFee", 3))
                        .contains("// 3 combinations for `shippingFee` offered no row:"),
                said(new GenerationReason.CombinationsWithheld("shippingFee", 3)));
    }

    private static String said(GenerationReason why) {
        return GeneratedRows.of("example.shipping",
                Map.of("shippingFee", new Adequacy.Filling(
                        new Generator.GenerationResult(List.of(), List.of(), List.of(why)),
                        Generator.GenerationResult.NONE, List.of())),
                Map.of(), false, SourceNameResolver.identity());
    }
}
