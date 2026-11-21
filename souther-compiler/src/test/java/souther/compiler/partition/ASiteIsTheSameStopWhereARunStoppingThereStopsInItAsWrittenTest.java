package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;

import java.math.BigInteger;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Another site is the same stop as an operation's where a run stopping there stops in the
 * operation as a finding says it: written the same, for the same kind of end, whatever ends each
 * is held to. That is not the operation told again, which asks the ends as well.
 */
class ASiteIsTheSameStopWhereARunStoppingThereStopsInItAsWrittenTest {

    private static final LinearForm<NumericTerm> X =
            LinearForm.atom(new NumericTerm.ValueOf(TermPath.of("x")));

    private static StopAssessment.Site.PastItsEnds past(LinearForm<NumericTerm> form,
                                                        long greatest,
                                                        boolean ofTheRepresentation) {
        return new StopAssessment.Site.PastItsEnds(
                UndividedByARelation.IntOperation.overTheInput(form, BigInteger.ZERO,
                        BigInteger.valueOf(greatest), List.of(), ofTheRepresentation));
    }

    @Test
    void endsApartAreOneStopThoughNotOneTelling() {
        StopAssessment.Site.PastItsEnds narrower = past(X, 10, true);
        StopAssessment.Site.PastItsEnds wider = past(X, 20, true);

        assertTrue(narrower.sameStopAs(wider));
        assertFalse(narrower.operation().sameOperationAs(wider.operation()));
    }

    @Test
    void anotherKindOfEndOrAnotherFormIsAnotherStop() {
        StopAssessment.Site.PastItsEnds ofTheType = past(X, 10, true);

        assertFalse(ofTheType.sameStopAs(past(X, 10, false)));
        assertFalse(ofTheType.sameStopAs(past(LinearForm.atomMinusConstant(
                new NumericTerm.ValueOf(TermPath.of("x")), ExactRatio.ONE), 10, true)));
    }
}
