package souther.compiler.coverage;

import java.util.Set;

/**
 * What one run of one row was seen to do, as a value nothing goes on changing.
 *
 * <p>One snapshot and not two channels. What is recorded has two shapes — the arms a run passed
 * through, and the ways the comparisons it evaluated came out — and they are taken together, of one
 * thread, between one {@code begin} and one {@code end}. Handed over as two values they would be two
 * things a reader could get from different runs, and a reader that asked for one of them would be
 * reasoning about a run it had only half of.
 *
 * <p><b>A family apiece, though the numbers come out of one counter.</b> One counter hands the
 * numbers out because the call a probed class makes carries one number and nothing else; that is a
 * fact about the instruction, and it is not a reason to write the two families into one set. Held
 * together, what a run did at an arm and what it did at a comparison are told apart by asking the
 * numbering which each number was issued to — which is the family being worked out again from a
 * number, by a reader, after the numbering already said it. Here the recording says it, because the
 * call that wrote each entry knew.
 *
 * <p>So a comparison is recorded by the way it came out and by nothing else: that a way out of it
 * exists <em>is</em> its having been reached, and there is no second bit to keep in step with. An
 * arm has no way out to record and is the number itself.
 *
 * <p><b>Numbers, and what numbering they are of.</b> A probed class is handed the number the
 * emitter wrote into the call and has no numbering to ask what it addresses, so what a run leaves
 * behind is numbers. What says which numbering they are of is the classes the run went through, and
 * this carries what those classes were emitted under. So the two halves of "where was this run
 * recorded" are here and nowhere else: a reader turns them into places by holding this against a
 * numbering ({@link SiteNumbering#align}), and one that does not match is refused rather than
 * answered.
 *
 * @param numbering   what the classes this run went through were numbered by
 * @param arms        the numbers of the arms the run was recorded at, which is what a branch
 *                    measure counts
 * @param comparisons the ways the comparisons it evaluated came out
 */
public record Observation(NumberingIdentity numbering, Set<Integer> arms,
                          Set<ComparisonOutcome> comparisons) {

    public Observation {
        if (numbering == null) {
            throw new IllegalArgumentException(
                    "a run was recorded under some numbering or its numbers mean nothing");
        }
        arms = arms == null ? Set.of() : Set.copyOf(arms);
        comparisons = comparisons == null ? Set.of() : Set.copyOf(comparisons);
        // And each number under the family the call that wrote it was for. Said here, where the
        // recording is made, rather than left to whoever reads it: a number written into the wrong
        // family is the emitter having lit a place it was not at, and a reader meeting it later has
        // a run that says something no run could say.
        //
        // Both ways out of one comparison together are not a breach and must not be refused: a
        // place a run comes back to is evaluated more than once, and a recording that held only
        // which way it went the first time would be saying less than it saw.
        for (int raw : arms) {
            requireIssuedTo(numbering, raw, SiteAddress.Arm.class, "an arm");
        }
        for (ComparisonOutcome way : comparisons) {
            requireIssuedTo(numbering, way.at(), SiteAddress.Comparison.class, "a comparison");
        }
    }

    private static void requireIssuedTo(NumberingIdentity numbering, int raw,
                                        Class<? extends SiteAddress> family, String what) {
        if (!family.isInstance(numbering.at(raw))) {
            throw new IllegalArgumentException(raw + " is recorded as " + what
                    + ", and the numbering handed it out for " + numbering.at(raw));
        }
    }
}
