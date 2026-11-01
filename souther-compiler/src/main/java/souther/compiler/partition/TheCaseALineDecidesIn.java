package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.meaning.Proposition;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.WholeNumberRuns;

import java.math.BigInteger;
import java.util.Map;
import java.util.Objects;
import java.util.concurrent.ConcurrentHashMap;

/**
 * The case a line of a statement of several decides in, where a row read back at a point of the
 * line has to be in it, with what it says of a remainder read once for each form and divisor
 * asked ({@link ResiduesAStatementLeaves}).
 *
 * <p>One for a line put to rows, asked at every value a point of it is searched with: the case is
 * the line's whatever value is tried, so what it says of a remainder is too.
 */
public final class TheCaseALineDecidesIn {

    private final Proposition decides;
    private final Map<ARemainder, WholeNumberRuns> read = new ConcurrentHashMap<>();

    TheCaseALineDecidesIn(Proposition decides) {
        this.decides = Objects.requireNonNull(decides, "a line decides in some case");
    }

    /** One remainder asked of the case: of a form by a divisor. */
    private record ARemainder(LinearForm<NumericTerm> dividend, BigInteger divisor) {}

    /** The remainders by {@code divisor} of {@code dividend} the case may hold at. */
    WholeNumberRuns remaindersOf(LinearForm<NumericTerm> dividend, BigInteger divisor) {
        return read.computeIfAbsent(new ARemainder(dividend, divisor),
                asked -> ResiduesAStatementLeaves.of(decides, asked.dividend(), asked.divisor()));
    }
}
