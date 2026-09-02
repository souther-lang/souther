package souther.compiler.partition;

import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.RunSensitivity;

/**
 * Why a reading of a number came to none.
 *
 * <p>Two kinds and neither outranks the other. A value the observation did not keep whole is a value
 * that is there, named by the code an observation writes; a walk that arrived at no value met none,
 * and has no such code. What a reader does about them differs — the first is something a wider
 * budget keeps and the second is not — so both travel, and a quantity stopped in both ways says
 * both.
 *
 * <p><b>Collected and never chosen between.</b> A rule over several terms is read once per term and
 * a point is tried against several readings of several rows, so the reasons arrive a few at a time
 * and are put together. Ranked instead, every place that folds them writes a precedence, every
 * precedence throws one away, and which one a report says comes out of the order a map or a list
 * happened to be walked in.
 */
public sealed interface ReadingGap {

    /**
     * Whether a run of this compiler that allows more could come to a different answer here.
     *
     * <p>Which is the difference this type's own comment already states — one is something a wider
     * budget keeps and the other is not — said as a value rather than as prose. Each arm asks
     * whatever holds the fact rather than answering for it: an observation that stopped carries the
     * code, and the code is what every producer of it agrees about.
     */
    RunSensitivity runSensitivity();

    /** The observation of a value did not come back whole, and this is what it met. */
    record Observation(Incompleteness.Code code) implements ReadingGap {

        public Observation {
            if (code == null) {
                throw new IllegalArgumentException("an observation that stopped says what it met");
            }
        }

        @Override
        public RunSensitivity runSensitivity() {
            return code.runSensitivity();
        }
    }

    /** The walk arrived at no value, so there was none to observe. */
    record NoValue() implements ReadingGap {

        /** Nothing was compared against a figure: the walk met no value, and it meets none however
         *  much a run is allowed. */
        @Override
        public RunSensitivity runSensitivity() {
            return RunSensitivity.UNAFFECTED;
        }
    }

    ReadingGap NO_VALUE = new NoValue();

    /** The gap an observation's code is, for a reader holding one. */
    static ReadingGap of(Incompleteness.Code code) {
        return new Observation(code);
    }
}
