package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;
import souther.compiler.meaning.Proposition;

import java.util.List;
import java.util.Optional;

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
 * <p><b>Only what can vary.</b> A part that comes out the same whatever the input is an answer and
 * not a question, so nobody owns it and it is not offered.
 */
final class WhatAForkTests {

    private WhatAForkTests() {}

    /** The parts the truth of {@code atom} turns on, each read where it stands. */
    static List<Denotation> partsOfTheAnswer(Core atom, WhatNamesStandFor names) {
        return Pullback.ofATruth(atom, names.reads(), names.read(), Optional.empty()).leaves()
                .stream()
                .filter(leaf -> !(leaf.part() instanceof Proposition.Unread unread
                        && unread.fixed()))
                .map(Pullback.Leaf::from)
                .toList();
    }
}
