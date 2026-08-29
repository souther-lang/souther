package souther.compiler.inputs;

import souther.compiler.check.Symbols;
import souther.compiler.core.Core;

/**
 * What a name in a tree stands for, and nothing about whether a row is ever written there.
 *
 * <p><b>The half of a reader that can be had before the input has been read.</b> Which location a
 * name points at is settled by the parameters, the bindings on the way, and the case an arm says the
 * value it matched turned out to be — all facts about the tree being walked. Whether a value stands
 * at that location, whether the rules leave the case anything, what the declarations there admit:
 * those are {@link InputDomain}'s, asked of it about the path this produced.
 *
 * <p><b>Held apart because the two cannot both be asked at once.</b> A reading of an input is built
 * over the paths a behavior's measurement names ({@link InputDemand}), so whatever finds those paths
 * runs before there is a reading to consult. A path environment that consulted one could not be used
 * to find them, and the two questions run together is what made the circle: a rule written one link
 * down a chain named no position, because the environment asked a reading that had not been told
 * about it yet.
 *
 * <p>So this is what a demand is collected through, and it is a capability rather than a type of its
 * own: {@link InputReads} is one, and hands out the same answers to everything that walks a body.
 * What it adds is the reading beside them, which is exactly what nothing collecting a demand may
 * reach.
 */
public interface InputPaths {

    /** The position {@code e} names here, or null where it names none. */
    TermPath pathOf(Core e, Symbols symbols);

    /** The same, inside what {@code binder} binds. */
    InputPaths and(Core.Binder binder, Core value);

    /** The same, inside one arm of a {@code match}. */
    InputPaths insideArm(Core.Match match, Core.Case arm, Symbols symbols);
}
