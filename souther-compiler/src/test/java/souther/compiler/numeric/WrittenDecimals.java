package souther.compiler.numeric;

import java.math.BigDecimal;

/**
 * A decimal a test has established the host has room to write, for the tests that ask which number
 * a ratio is rather than whether the host could write it out.
 *
 * <p>Null where no decimal is the number, as the total member answers with an empty one. The tests
 * that ask whether the host had room read {@link ExactRatio#writtenDecimal} itself.
 */
final class WrittenDecimals {

    private WrittenDecimals() {
    }

    static BigDecimal of(ExactRatio number) {
        return number.writtenDecimal()
                .orFail("a number the test asks the digits of has room to be written").orElse(null);
    }
}
