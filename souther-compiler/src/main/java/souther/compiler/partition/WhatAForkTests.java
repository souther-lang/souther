package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhyUnread;

import java.util.List;

/**
 * Which parts a fork's answer turns on, each with the expression it was read off.
 *
 * <p>What the fork tests states a proposition ({@link Pullback}), carried back through what the
 * library says its operations do and nowhere else: {@code List.any(p, xs)} turns on what {@code p}
 * answers, and so does whether {@code List.filter(p, xs)} holds anything, while whether
 * {@code List.map(p, xs)} does turns on {@code xs} alone. The parts are the ones that proposition
 * is made of, read once, so a reader asking who owns a part and a reader asking what the fork
 * states are asking about the same parts.
 *
 * <p><b>The parts and not whether one of them was found.</b> Which of them a reader owns is a
 * question about each of them: a closure answering {@code p.age > 18 && List.contains(0, p.tags)}
 * states a comparison and something nothing here reads, and the fork around the operation states
 * the second whoever owns the first.
 *
 * <p><b>Only what can vary, read off the proposition.</b> A part that comes out the same whatever
 * the input is an answer and not a question, so nobody owns it and it is not offered — and whether
 * a part varies is a question about where it stands in what the fork states, not about the part on
 * its own ({@link Pullback.Pulled#turnsOn}).
 */
final class WhatAForkTests {

    private WhatAForkTests() {}

    /**
     * What was read of the parts an answer turns on.
     *
     * <p>A proposition a reading stopped in at a figure states the parts it got to, and where it
     * got to is where the figure ran out and not what the answer turns on: the parts of one that
     * stopped are no list of the parts there are, and a part missing from it was not found absent.
     * A part nothing reads is a part of the answer all the same, and does not make it incomplete.
     */
    sealed interface PartsRead {

        /** The proposition was read to the end, so these are all the parts the answer turns on. */
        record Complete(List<Denotation> parts) implements PartsRead {}

        /** The proposition was stopped in at a figure, and says nothing of which parts there are. */
        record Incomplete(List<WhyUnread> stoppedFor) implements PartsRead {

            public Incomplete {
                stoppedFor = List.copyOf(stoppedFor);
            }
        }
    }

    /** The parts the truth of {@code atom} turns on, each read where it stands. */
    static List<Denotation> partsOfTheAnswer(Core atom, WhatNamesStandFor names) {
        return partsOf(pulled(atom, names));
    }

    /** What was read of the parts the truth of {@code atom} turns on. */
    static PartsRead partsRead(Core atom, WhatNamesStandFor names) {
        Pullback.Pulled truth = pulled(atom, names);
        List<WhyUnread> stops = Proposition.stopsIn(truth.proposition());
        return stops.stream().anyMatch(why -> why.figure().isPresent())
                ? new PartsRead.Incomplete(stops)
                : new PartsRead.Complete(partsOf(truth));
    }

    private static Pullback.Pulled pulled(Core atom, WhatNamesStandFor names) {
        return WhatConditionsState.of(names.read()).truth(atom, names.reads(), names.read());
    }

    private static List<Denotation> partsOf(Pullback.Pulled truth) {
        return truth.turnsOn().stream().map(Pullback.Leaf::from).toList();
    }
}
