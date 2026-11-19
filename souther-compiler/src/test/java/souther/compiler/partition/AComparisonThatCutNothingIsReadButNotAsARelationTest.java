package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A comparison read to the end that cut nothing is read, and as no relation of the input's
 * numbers ({@link ComparisonAssessment#readAsARelation}): what the stops of its evaluation say is
 * asked of a comparison read as one.
 */
class AComparisonThatCutNothingIsReadButNotAsARelationTest {

    @Test
    void aComparisonThatCutNothingIsReadAsNoRelation() {
        assertFalse(new ComparisonAssessment.CutsNothing(List.of()).readAsARelation());
    }
}
