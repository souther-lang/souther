package souther.compiler.reach;

import souther.compiler.coverage.ArmProbe;

/**
 * What shows that something arrives.
 *
 * <p>Never "the reading found no contradiction", which is a fact about the reading. The reader that
 * acts on a {@link Reachability.Reachable} refutes something an author wrote, so what it rests on
 * has to be about the program: a run that went through, or a rule that settles the question
 * completely. A value put together would be a third and nothing builds one yet — the day something
 * does, it is an arm here and a sentence in whoever writes them.
 *
 * <p>Payload, like {@link Proof}, and its arms are not types anything outside this package can
 * name. Nothing writes a sentence about one yet, so there is no {@code Words} for it either; the
 * day a reader needs one, it is added here and every arm answers it or nothing compiles.
 */
public sealed interface Witness permits ARunWentThrough, EveryRuleReadAndNothingAbove {

    /** @see ARunWentThrough */
    static Witness aRunWentThrough(ArmProbe probe) {
        return new ARunWentThrough(probe);
    }

    /** @see EveryRuleReadAndNothingAbove */
    static Witness everyRuleReadAndNothingAbove(String position) {
        return new EveryRuleReadAndNothingAbove(position);
    }
}

/**
 * A run went through it.
 *
 * <p>The plainest of them, and the only one that is an observation rather than an argument. It also
 * settles a proof that said otherwise: what a row did happened, so a reading that ruled it out was
 * wrong about the model rather than the row being wrong about the rules.
 */
record ARunWentThrough(ArmProbe probe) implements Witness {}

/**
 * The rules leave the case standing, every rule reaching the position was read, and nothing stands
 * between here and being applied at all.
 *
 * <p>Complete on its own terms, which is what makes it a witness and not an absence of proof: the
 * admission is claimed only where the reading ran to the end, and the fork being the first thing the
 * body does means reaching it is what applying the behavior is.
 */
record EveryRuleReadAndNothingAbove(String position) implements Witness {}
