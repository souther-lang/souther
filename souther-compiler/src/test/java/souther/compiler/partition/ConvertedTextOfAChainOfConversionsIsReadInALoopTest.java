package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Quantity;
import souther.compiler.semantics.CaseMapping;
import souther.compiler.types.ValueName;

import java.time.Duration;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

/**
 * How many case conversions a text is made by is the model's, so what a text is made of is read
 * without a frame for each of them.
 */
class ConvertedTextOfAChainOfConversionsIsReadInALoopTest {

    private static final ValueName.Stdlib LOWERCASE = ValueName.Stdlib.operation("String",
            "lowercase");

    private static final ValueName.Stdlib UPPERCASE = ValueName.Stdlib.operation("String",
            "uppercase");

    private static final ValueName.Stdlib TRIM = ValueName.Stdlib.operation("String", "trim");

    private static final NumericTerm.ValueOf PLACE = new NumericTerm.ValueOf(
            TermPath.of("i").then("s"));

    private static Quantity converted(int calls, ValueName.Stdlib operation) {
        Quantity answer = new DecisionAtom.OfTheInput(PLACE);
        for (int i = 0; i < calls; i++) {
            answer = new Quantity.WhatAnOperationAnswers(operation, List.of(answer));
        }
        return answer;
    }

    @Test
    void aTextMadeOfTheInputByConversionsIsThePlaceAndWhatTheyMakeOfIt() {
        ConvertedText text = ConvertedText.of(converted(2, LOWERCASE));
        assertEquals(PLACE, text.place());
        assertEquals(new CaseMapping.Lowercase(CaseMapping.LOWERCASE), text.through());
        assertEquals(CaseMapping.NONE, ConvertedText.of(new DecisionAtom.OfTheInput(PLACE)).through());
    }

    @Test
    void aTextMadeByAnythingElseIsNone() {
        assertNull(ConvertedText.of(converted(3, TRIM)));
        Quantity inner = converted(3, TRIM);
        assertNull(ConvertedText.of(new Quantity.WhatAnOperationAnswers(UPPERCASE, List.of(inner))));
    }

    @Test
    void aChainAHundredThousandConversionsLongIsReadWithoutOverflowingTheStack() {
        Quantity deep = converted(100_000, LOWERCASE);
        assertNotNull(assertTimeoutPreemptively(Duration.ofSeconds(10),
                () -> ConvertedText.of(deep)));
        assertNull(assertTimeoutPreemptively(Duration.ofSeconds(10),
                () -> ConvertedText.of(new Quantity.WhatAnOperationAnswers(TRIM, List.of(deep)))));
    }
}
