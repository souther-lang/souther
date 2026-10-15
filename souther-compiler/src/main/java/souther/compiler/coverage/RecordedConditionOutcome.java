package souther.compiler.coverage;

/**
 * One condition coming out one way, as a run records it.
 *
 * <p>Recorded from the condition's own value and never worked out from the arm that follows it. A
 * condition made of several stops as soon as it is settled, so under {@code A && B} the arm taken
 * when the whole fails is reached both by a value that made {@code B} false and by one that never
 * evaluated {@code B} — the arm cannot say which, and a reading that recovered the way out of it
 * would be guessing at exactly the point a claim about {@code B} is made.
 *
 * <p>Three states and not two, which is what having these at all buys. A condition can have come
 * out one way, come out the other, or not have been reached: the first two are one of these being
 * recorded and the third is neither of them being, and nothing else in a run's record can tell the
 * third from the other two.
 *
 * <p>Written in the emitter's vocabulary, which is the one a run is recorded in. What a probed class
 * calls is {@code Probe.condition} with the number the emitter put in the call, and nothing running
 * has a catalog to say which construct that is. Which construct a reading is talking about is
 * {@link souther.compiler.types.ConstructOccurrence}, and the plan is what turns one into the
 * other.
 *
 * <p><b>The number and not an address.</b> A probed class is handed the number the emitter wrote
 * into the call and has no numbering to ask what it addresses; a recording is what that class left
 * behind, so it is written in numbers. Joining one back to the place it was issued for is the other
 * side of that boundary and belongs there — a recording that carried an address would be carrying
 * an answer nothing running could have given.
 *
 * @param at   the number the run was recorded at
 * @param held the way it came out
 */
public record RecordedConditionOutcome(int at, boolean held) {

    public RecordedConditionOutcome {
        if (at < 0) {
            throw new IllegalArgumentException(
                    "a run is recorded at a number the emitter wrote: " + at);
        }
    }

    @Override
    public String toString() {
        return "site@" + at + (held ? " held" : " failed");
    }
}
