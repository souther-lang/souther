package souther.compiler.partition;

import souther.compiler.values.InOneOrder;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/**
 * What became of each thing a plan asked a generation for, held against that plan.
 *
 * <p>A total function over {@link GenerationPlan#obligations}: every obligation the plan named has
 * exactly one {@link GenerationAnswer} here, filed under itself, and the constructor is where that
 * is settled — so a discharge with one obligation missing or one nobody asked about is not a value
 * this can build, rather than a mismatch a reader downstream has to find by comparing this against
 * the plan a second time. What used to be four parallel maps compared against four parallel
 * projections of the plan is one map compared against the one list the plan already holds; a kind
 * added to {@link GenerationObligation} without an entry here does not build, which is what keeps
 * this from opening the same universe the plan already closed back into a product of its own.
 *
 * <p>Held in no order at all. What a row is offered for is taken in the plan's order ({@link
 * #inPlanOrder}) and everything else asks by key, so two runs that answered the same obligations
 * in two orders are one discharge — and an order kept here would be one a reader could start
 * reading and a sentence could start saying. What is written out is written in one order ({@link
 * #toString}), which is what a message about one run reading the same way twice wanted of it.
 *
 * <p><b>{@link #answers} is the one canonical map, and the sole authority for every view below
 * it.</b> {@link #classes} and {@link #pairs} are read off {@code answers} on every call rather
 * than cached beside it, and so is a single-obligation lookup at a class, a pair or a meeting: it
 * wraps the target in the obligation it belongs to and asks {@code answers} directly, which costs
 * no walk of the others. {@link #arms} is the one projection still cached — {@link
 * #at(souther.compiler.coverage.ArmProbe)} is asked once per finding of a behavior, over every
 * arm, by a reader holding no obligation to wrap a key from; caching it once here is what spares
 * that reader the walk of every answer {@code arms} would otherwise cost on every finding. See
 * {@link GenerationAnswer} for why the values these project are not one shared disposition type
 * either.
 *
 * <p>Not a record, for the same reason: what {@link #equals} and {@link #hashCode} answer with is
 * {@link #plan} and {@link #answers} alone, held in no order — the derived views are computed from
 * those two and add nothing a record's generated equality would need to see.
 */
public final class Discharge {

    private final GenerationPlan plan;
    private final Map<GenerationObligation, GenerationAnswer> answers;
    private final Map<Generator.ArmOwed, ArmDisposition> arms;

    public Discharge(GenerationPlan plan, Map<GenerationObligation, GenerationAnswer> answers) {
        Objects.requireNonNull(plan, "a discharge answers a plan");
        Map<GenerationObligation, GenerationAnswer> validated = Ordered.byKey(answers);
        for (Map.Entry<GenerationObligation, GenerationAnswer> each : validated.entrySet()) {
            if (!each.getKey().equals(each.getValue().obligation())) {
                throw new IllegalArgumentException(
                        "an answer filed under an obligation it does not answer: " + each.getKey()
                                + " holds " + each.getValue());
            }
        }
        Set<GenerationObligation> asked = new LinkedHashSet<>(plan.obligations());
        if (!validated.keySet().equals(asked)) {
            throw new IllegalStateException(
                    "the obligations this run was asked for and the ones it answered for are not"
                            + " the same: asked " + InOneOrder.of(asked)
                            + ", answered " + InOneOrder.of(validated.keySet()));
        }
        this.plan = plan;
        this.answers = validated;
        // The one projection worth walking once here rather than rebuilding on every finding a
        // reader asks at(ArmProbe) for — see the class comment.
        Map<Generator.ArmOwed, ArmDisposition> arms = new LinkedHashMap<>();
        for (GenerationAnswer each : validated.values()) {
            if (each instanceof GenerationAnswer.Arm(var obligation, var disposition)) {
                arms.put(obligation.target(), disposition);
            }
        }
        this.arms = Collections.unmodifiableMap(arms);
    }

    /**
     * The answers taken over the plan, one apiece and in the plan's order.
     *
     * <p>Refuses two answers to the same obligation rather than silently keeping the first and
     * dropping the second: "exactly one answer" is what a total function over the plan means, and
     * an unchecked {@code putIfAbsent} would let the constructor's totality check pass on the
     * strength of whichever one it kept.
     */
    public static Discharge of(GenerationPlan plan, List<GenerationAnswer> answers) {
        Map<GenerationObligation, GenerationAnswer> byObligation = new LinkedHashMap<>();
        for (GenerationAnswer each : answers) {
            GenerationAnswer already = byObligation.putIfAbsent(each.obligation(), each);
            if (already != null) {
                throw new IllegalArgumentException(
                        "one obligation answered twice: " + already + " and " + each);
            }
        }
        return new Discharge(plan, byObligation);
    }

    /** Nothing asked for and nothing answered, which is the only run an empty plan is right for. */
    public static Discharge nothingAskedOf(GenerationPlan plan) {
        return new Discharge(plan, Map.of());
    }

    /** What this run was asked for. */
    public GenerationPlan plan() {
        return plan;
    }

    /** The answers, filed by the obligation each is to, held in no order. */
    public Map<GenerationObligation, GenerationAnswer> answers() {
        return answers;
    }

    /** Every answer, in the plan's own order. */
    public List<GenerationAnswer> inPlanOrder() {
        return plan.obligations().stream().map(answers::get).toList();
    }

    /** What became of each thing asked for, written in one order — see {@link InOneOrder}. */
    @Override
    public String toString() {
        return "answers " + InOneOrder.of(inPlanOrder());
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof Discharge that
                && plan.equals(that.plan) && answers.equals(that.answers);
    }

    @Override
    public int hashCode() {
        return Objects.hash(plan, answers);
    }

    /** One class of one position apiece, or none where the plan named none. */
    public Map<ClassOfAPosition, ClassDisposition> classes() {
        Map<ClassOfAPosition, ClassDisposition> out = new LinkedHashMap<>();
        for (GenerationAnswer each : answers.values()) {
            if (each instanceof GenerationAnswer.Class(var obligation, var disposition)) {
                out.put(obligation.target(), disposition);
            }
        }
        return Collections.unmodifiableMap(out);
    }

    /** One arm apiece, or none where the plan named none. */
    public Map<Generator.ArmOwed, ArmDisposition> arms() {
        return arms;
    }

    /** One combination of two classes apiece, or none where the plan named none. */
    public Map<ObligationIdentity.OfAFallbackPairCell, ClassDisposition> pairs() {
        Map<ObligationIdentity.OfAFallbackPairCell, ClassDisposition> out = new LinkedHashMap<>();
        for (GenerationAnswer each : answers.values()) {
            if (each instanceof GenerationAnswer.Pair(var obligation, var disposition)) {
                out.put(obligation.target(), disposition);
            }
        }
        return Collections.unmodifiableMap(out);
    }

    /** What became of one combination of the body's decisions, or null where nothing asked. */
    public ClassDisposition at(ObligationIdentity.OfACombinationOfDecisions owed) {
        return answers.get(new GenerationObligation.Meeting(owed))
                instanceof GenerationAnswer.Meeting(var _, var disposition) ? disposition : null;
    }

    /** What became of one combination of two classes, or null where nothing asked about it. */
    public ClassDisposition at(ObligationIdentity.OfAFallbackPairCell owed) {
        return answers.get(new GenerationObligation.Pair(owed))
                instanceof GenerationAnswer.Pair(var _, var disposition) ? disposition : null;
    }

    /** What became of one class, or null where this run was not asked about it. */
    public ClassDisposition at(ClassOfAPosition owed) {
        return answers.get(new GenerationObligation.Class(owed))
                instanceof GenerationAnswer.Class(var _, var disposition) ? disposition : null;
    }

    /** What became of one arm, or null where this run was not asked about it. */
    public ArmDisposition at(Generator.ArmOwed owed) {
        return arms.get(owed);
    }

    /**
     * The same, asked at one of the places a run through the arm is recorded.
     *
     * <p>For a reader holding an occurrence rather than the arm — a finding names one site of the
     * arm it is about, and what the search was asked for is the arm and every splice of it. Asked
     * with the site's own probe as though it were the whole key, such a reader found nothing
     * whenever the arm stood in the body more than once.
     *
     * <p>Every entry read and not the first that matches. A probe is one place in one body, so at
     * most one arm is recorded at it — and answered with whichever entry came first, two writings
     * of one discharge would answer a reader two ways wherever that stopped being true. So the
     * answer is the one arm claiming the place, and several claiming it is refused.
     *
     * <p>Counted rather than gathered. What the refusal has to say is that a place is held twice,
     * and which arms those are is read off the discharge by whoever is looking — gathered here they
     * would be named in the order the entries happen to be held, which is the order this says
     * nothing is answered from.
     */
    public ArmDisposition at(souther.compiler.coverage.ArmProbe probe) {
        ArmDisposition only = null;
        int claiming = 0;
        for (Map.Entry<Generator.ArmOwed, ArmDisposition> each : arms.entrySet()) {
            if (each.getKey().recordedAt(probe)) {
                claiming++;
                only = each.getValue();
            }
        }
        if (claiming > 1) {
            throw new IllegalStateException("a place is recorded against more than one arm: "
                    + probe + " is held by " + claiming + " of them");
        }
        return only;
    }
}
