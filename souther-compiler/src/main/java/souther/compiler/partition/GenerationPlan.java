package souther.compiler.partition;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * What one run of the generator searches for, in the search's own words.
 *
 * <p>A class of a position no row sits in, an arm of the body no row goes through, a combination of
 * two classes no row is in, a meeting of the body's decisions no row makes. Which of them a run is
 * asked about is established by whoever read the rows ({@code Adequacy.RowsOwed}) and handed here
 * whole — so a search does not work the list out a second time, and nothing downstream decides from
 * what a search happened to touch. What is owed at the lines a behavior's rules draw is owed too
 * and is not here: those rows are composed by the boundary search, which is asked in its own right.
 *
 * <p><b>Settled before anything that can stop the run.</b> The classes would not link, the rows
 * could not be read: each of those ends a generation, and each used to end it somewhere that had
 * never asked what was owed. What a reader of such a result got was a reason about the run and no
 * word about the thing they were asking after. Made here, every way out holds the same list.
 *
 * <p><b>One list, held as itself and not rebuilt from four kept beside it.</b> {@link
 * #classesOwed}, {@link #armsOwed}, {@link #pairsOwed} and {@link #meetingsOwed} are projections
 * of {@link #obligations}, read by whoever wants one kind on its own; {@link #obligations} is what
 * this holds. A kind added beside these four used to be a list nobody carrying a plan had to touch
 * to keep compiling — which is exactly how a search composing a row for it and an account reading
 * what was asked for came apart. Sealed under {@link GenerationObligation}, a fifth kind is a
 * permitted subtype nothing here can be written without a case for, so the same mistake does not
 * compile a second time.
 *
 * <p><b>Lists rather than sets, and the order is the contract.</b> What a row is composed for is
 * written out beside it, and the order those are written in is this order — so a plan handed over
 * as a set would leave the rows of one model coming out in whatever order a hash gave them, which
 * is not the same order twice. Each obligation appears once, which is the whole of what being a set
 * gave.
 *
 * @param subject     the behavior a row would be written for
 * @param obligations every class, arm, combination of two classes and meeting of the body's
 *                    decisions this run is asked for, in the order gathered — classes, then arms,
 *                    then the combinations of two classes, then the meetings, which is the order
 *                    {@link #of} takes them in and the order {@link #obligations()} hands them back
 */
public record GenerationPlan(MeasuredInput subject, List<GenerationObligation> obligations) {

    public GenerationPlan {
        obligations = List.copyOf(obligations);
        if (subject == null) {
            throw new IllegalArgumentException("a generation is asked for on behalf of a subject");
        }
        Set<GenerationObligation> seen = new LinkedHashSet<>(obligations);
        if (seen.size() != obligations.size()) {
            throw new IllegalArgumentException(
                    "the same obligation is owed twice in one plan: " + obligations);
        }
        // A class of another behavior, which is the same disagreement a measured input refuses among its
        // axes. Held here, one run would be answering for two behaviors and every sentence about
        // what it was asked for would be right about one of them.
        for (GenerationObligation each : obligations) {
            if (each instanceof GenerationObligation.Class(var target)
                    && !target.at().behavior().equals(subject.behavior())) {
                throw new IllegalArgumentException(
                        "a class of " + target.at().behavior() + " in the plan for "
                                + subject.behavior() + ": " + target);
            }
        }
    }

    /**
     * A plan over the four kinds an obligation is gathered as, in the order they were gathered.
     *
     * <p>What every caller outside this file holds: a search gathers its classes, its arms, its
     * combinations of two classes and its meetings apart, because each kind is looked for its own
     * way, and this is where the four are put end to end into the one list {@link #obligations}
     * holds.
     */
    public static GenerationPlan of(MeasuredInput subject, List<ClassOfAPosition> classesOwed,
                                    List<Generator.ArmOwed> armsOwed,
                                    List<ObligationIdentity.OfAFallbackPairCell> pairsOwed,
                                    List<ObligationIdentity.OfACombinationOfDecisions>
                                            meetingsOwed) {
        List<GenerationObligation> out = new ArrayList<>();
        classesOwed.forEach(each -> out.add(new GenerationObligation.Class(each)));
        armsOwed.forEach(each -> out.add(new GenerationObligation.Arm(each)));
        pairsOwed.forEach(each -> out.add(new GenerationObligation.Pair(each)));
        meetingsOwed.forEach(each -> out.add(new GenerationObligation.Meeting(each)));
        return new GenerationPlan(subject, out);
    }

    /** Whether anything at all is owed, which is what a run with nothing to do looks like. */
    public boolean isEmpty() {
        return obligations.isEmpty();
    }

    /** One class of one position apiece, in the order they were gathered. */
    public List<ClassOfAPosition> classesOwed() {
        List<ClassOfAPosition> out = new ArrayList<>();
        for (GenerationObligation each : obligations) {
            if (each instanceof GenerationObligation.Class(var target)) {
                out.add(target);
            }
        }
        return List.copyOf(out);
    }

    /** One arm apiece, in the order the plan numbered them. */
    public List<Generator.ArmOwed> armsOwed() {
        List<Generator.ArmOwed> out = new ArrayList<>();
        for (GenerationObligation each : obligations) {
            if (each instanceof GenerationObligation.Arm(var target)) {
                out.add(target);
            }
        }
        return List.copyOf(out);
    }

    /**
     * One combination of two classes apiece, where the pair space is the criterion this behavior
     * is held to. Beside the classes and not among them: a class is met by a value falling in it,
     * and one of these by two values falling in two — so a row for each of two classes is two rows
     * and neither shows what the behavior does where both hold.
     */
    public List<ObligationIdentity.OfAFallbackPairCell> pairsOwed() {
        List<ObligationIdentity.OfAFallbackPairCell> out = new ArrayList<>();
        for (GenerationObligation each : obligations) {
            if (each instanceof GenerationObligation.Pair(var target)) {
                out.add(target);
            }
        }
        return List.copyOf(out);
    }

    /**
     * One combination of the body's decisions apiece, where those are the criterion this behavior
     * is held to. Beside the arms and not among them: an arm is a place a run is at, and one of
     * these is several decisions settling one value — so rows through every arm can leave one of
     * these unmade, which is the whole reason it is asked about.
     */
    public List<ObligationIdentity.OfACombinationOfDecisions> meetingsOwed() {
        List<ObligationIdentity.OfACombinationOfDecisions> out = new ArrayList<>();
        for (GenerationObligation each : obligations) {
            if (each instanceof GenerationObligation.Meeting(var target)) {
                out.add(target);
            }
        }
        return List.copyOf(out);
    }
}
