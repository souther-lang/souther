package souther.compiler.coverage;

/**
 * One comparison of one body, as the thing a rule is read off and a run is recorded at.
 *
 * <p>What a reading of the model joins on. A line drawn on a comparison, a decision said of it and a
 * hit recorded at it are three readers of one place, and each of them used to hold the node the
 * comparison was recognised from and match on that. That made the tree the join key: two readers
 * agreeing meant they were holding the same object, which nothing outside one walk of one tree can
 * be held to.
 *
 * <p><b>Issued by {@link ComparisonCatalog}.</b> The catalog is the one enumeration of what the
 * bodies of a module hold, so an occurrence exists for every comparison there is one of, whether or
 * not anything measures it. A second place making one would be a second enumeration handing out
 * names for one thing, with nothing to say which name a reader was holding — which is a rule about
 * the compiler and not about the type: what is written here is a pair of ordinary values, and
 * {@code WhoNamesAComparisonAndWhoAddressesOneTest} is what holds the compiler to one maker of
 * them. A test fixture that writes a report about a comparison nothing compiled makes one by hand,
 * and that is a fixture standing in for a catalog.
 *
 * <p><b>Not the emitter's number.</b> Where a run through this is recorded is
 * {@link ComparisonEmissionSite}, which the plan hands out for the comparisons it instruments —
 * fewer than these, because a comparison behind an abort is one no run reaches. Held as one value,
 * "which comparison is this" and "where is a run through it written down" were one question, and
 * the answer to the first was only ever as complete as the second.
 *
 * <p>Occurrence and not comparison: a non-recursive helper is spliced into each body that calls it,
 * so one comparison the author wrote is several here, each reached under its caller's own
 * conditions.
 *
 * <p><b>Named in the set it travels in, which is wider than the catalog that issued it.</b> A
 * catalog is of one module, and two modules may each declare a {@code check} whose body writes a
 * comparison first — so a behavior's name and a number tell those two apart nowhere. The node this
 * replaced was distinct across everything there is, being an object; a name that is distinct only
 * within a module would be a narrower identity wearing the same job, and the crossing this exists
 * to be the only one of would join one module's reading to another module's comparison and say
 * nothing.
 *
 * @param module   whose module the body is in
 * @param behavior whose body it stands in
 * @param ordinal  which of that body's comparisons it is, in the order the source wrote them. The
 *                 order is the walk's, which is a function of the body alone — the emitter builds
 *                 one catalog and a measurement builds another, and a reading joining across the
 *                 two is joining on this
 */
public record ComparisonOccurrence(String module, String behavior, int ordinal) {

    public ComparisonOccurrence {
        if (module == null || behavior == null) {
            throw new IllegalArgumentException(
                    "a comparison of a body is one of somebody's body, in somebody's module");
        }
        if (ordinal < 0) {
            throw new IllegalArgumentException(
                    "a comparison stands somewhere among the body's: " + ordinal);
        }
    }

    @Override
    public String toString() {
        return "comparison " + ordinal + " of " + module + "." + behavior;
    }
}
