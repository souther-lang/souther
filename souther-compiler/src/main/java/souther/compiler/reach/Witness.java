package souther.compiler.reach;

/**
 * What shows that something arrives.
 *
 * <p>Three ways and no fourth, because the fourth would be "the reading found no contradiction" —
 * which is a fact about the reading. The reader that acts on a {@link Reachability.Reachable}
 * refutes something an author wrote, so what it rests on has to be about the program.
 *
 * <p>Payload, like {@link Proof}. Taken apart by the renderer and by nothing that decides anything.
 */
public sealed interface Witness {

    /**
     * A run went through it.
     *
     * <p>The plainest of the three, and the only one that is an observation rather than an
     * argument. It also settles a proof that said otherwise: what a row did happened, so a reading
     * that ruled it out was wrong about the model rather than the row being wrong about the rules.
     *
     * @param probe where the run was recorded
     */
    record ARunWentThrough(int probe) implements Witness {}

    /**
     * The rules leave the case standing, every rule reaching the position was read, and nothing
     * stands between here and being applied at all.
     *
     * <p>Complete on its own terms, which is what makes it a witness and not an absence of proof:
     * the admission is claimed only where the reading ran to the end, and the fork being the first
     * thing the body does means reaching it is what applying the behavior is.
     */
    record EveryRuleReadAndNothingAbove(String position) implements Witness {}

    /**
     * A value that reaches it was put together.
     *
     * <p>The general form, and the one that answers wherever the other two do not. Nothing builds
     * one of these yet; the arm is here because leaving it out would make the two above read as the
     * definition of arriving rather than as two ways of showing it.
     *
     * @param written the value, as a row would be written with it
     */
    record AValueThatReachesIt(String written) implements Witness {}
}
