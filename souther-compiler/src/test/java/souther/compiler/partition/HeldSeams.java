package souther.compiler.partition;

import souther.compiler.numeric.Towards;

/**
 * A seam a test has established is worked out, for the tests that ask what a seam says rather than
 * whether it could be worked out.
 *
 * <p>The tests that ask the second question call {@link Seam#of} and read the answer.
 */
final class HeldSeams {

    private HeldSeams() {
    }

    static Seam of(LevelSpace space, Level cut, Towards belongsTo) {
        return Seam.of(space, cut, belongsTo).orFail("a seam the test asks for is worked out");
    }

    static Seam of(LevelSpace space, Level cut, Towards belongsTo, Seam.Scale into) {
        return Seam.of(space, cut, belongsTo, into)
                .orFail("a seam the test asks for is worked out");
    }
}
