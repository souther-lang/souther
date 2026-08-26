package souther.compiler.partition;

/**
 * What a reading of a rule recorded about the line it drew.
 *
 * <p>One projection and not three questions. Each of these is a fact some producer wrote down and
 * every consumer of a line wants. Asked one at a time, each answer is a switch over the arms an
 * {@link OriginRef} has, written wherever the answer is wanted, and two such switches are free to
 * fill one slot differently — a slot a rule leaves empty is then filled by whoever is reading rather
 * than by whoever knows. Kept as one value, a rule answers all three where it is written and no
 * consumer has a slot to fill in for it.
 *
 * <p>Worked out once from what the producer knows, and never worked back out of what came later. A
 * bound records which way it keeps its values and whether it admits the value it stops at, and which
 * side of the line that value is on follows from the two — so it is settled here, beside the rule
 * that knows both, rather than by a consumer holding the range every rule together left.
 *
 * <p>And what a border <em>makes</em> of these — which way the rule is satisfied from its line,
 * whether it orders the values around it at all, which of the four points a row stands at — is
 * {@link Border}'s, derived there from these and derived nowhere else. A reading says what it read,
 * and a measure says what that means for the rows it asks for.
 *
 * @param valueBelongsBelow which side of the line the cut value itself is on. For a rule that orders
 *                          the values around its line it decides which neighbour is the other
 *                          class's edge: {@code <= 3000} leaves 3001 over there, {@code < 3000}
 *                          leaves 2999. For a bound, which orders nothing across its line because
 *                          nothing outside it can be constructed, it is still an answer — the value
 *                          a bound stops at is one it keeps or one it leaves, and which of the two
 *                          says which way the bound runs
 * @param holdsAtTheValue   whether the rule is true at the line's own value, which is what says
 *                          whether a row there is the border's {@code ON} point or its {@code OFF}
 *                          point. Not derivable from {@code valueBelongsBelow}: {@code x <= c} and
 *                          {@code x > c} agree about the class the value is in and disagree here
 * @param singles           whether the rule singles the value out rather than ordering the values
 *                          either side of it. False of a bound, and not because a bound has nothing
 *                          to say: a bound keeps a run of the order and the run is what it is about,
 *                          which is a different thing from the far side holding no value
 */
public record LineFacts(boolean valueBelongsBelow, boolean holdsAtTheValue, boolean singles) {}
