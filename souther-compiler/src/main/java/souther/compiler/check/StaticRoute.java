package souther.compiler.check;

/**
 * One way a guard could discharge one part of a clause.
 *
 * <p>A route and not a discharge. This says the check carried the part into a form a guard can be
 * held against; whether any guard did is asked at the construction, from what the guards on that
 * path established, and is {@link Predicates.Clause#dischargedBy}'s to answer. Named for what the
 * check managed, {@code AsABound} would read as "discharged" the first time somebody needed it to,
 * and a report would say a construction was proven by a classification that never saw one.
 *
 * <p>The routes of one part are alternatives: any of them discharges it, which is what the check
 * does with them. The parts themselves are not — every part of a clause has to be discharged for the
 * clause to be, which is why they are held apart ({@link RequiredPart}).
 */
public sealed interface StaticRoute {

    /**
     * A relation the numeric domain reasons over, so any guard that <em>implies</em> it discharges
     * the part.
     *
     * <p>Reading the same relation as the cases of whatever chooses inside it is not a route of its
     * own. It is only ever built beside this one — a clause with no relation has no cases to read
     * either — so it widens what discharges this route rather than offering an author another.
     */
    record AsABound() implements StaticRoute {}

    /**
     * A term the check can name but not reason about, so a guard establishing the same canonical
     * property discharges the part and nothing weaker does.
     */
    record AsATerm() implements StaticRoute {}
}
