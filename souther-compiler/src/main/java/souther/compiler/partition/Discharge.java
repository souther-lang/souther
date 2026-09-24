package souther.compiler.partition;

import souther.compiler.coverage.ArmProbe;
import souther.compiler.values.InOneOrder;

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
 * <p><b>{@link #answers} is the one canonical map, and the sole authority for every reader
 * below it.</b> A single-obligation lookup wraps the target in the obligation it belongs to and
 * asks {@code answers} directly, which costs no walk of the others — so there is nothing to
 * project as a whole map, and no reader asks for one; a caller that wants every class or every arm
 * filters {@link #answers} itself. A reader holding one place an arm is recorded at rather than
 * the arm asks the plan which arm that place belongs to ({@code GenerationPlan.armAt}) and then
 * asks {@code answers}: which arm a place belongs to is what the plan asked for, and nothing a run
 * answered. See {@link GenerationAnswer} for why the values these answer with are not one shared
 * disposition type either.
 *
 * @param plan    what this run was asked for
 * @param answers the answers, filed by the obligation each is to, held in no order
 */
public record Discharge(GenerationPlan plan, Map<GenerationObligation, GenerationAnswer> answers) {

    public Discharge {
        Objects.requireNonNull(plan, "a discharge answers a plan");
        answers = Ordered.byKey(answers);
        for (Map.Entry<GenerationObligation, GenerationAnswer> each : answers.entrySet()) {
            if (!each.getKey().equals(each.getValue().obligation())) {
                throw new IllegalArgumentException(
                        "an answer filed under an obligation it does not answer: " + each.getKey()
                                + " holds " + each.getValue());
            }
        }
        Set<GenerationObligation> asked = new LinkedHashSet<>(plan.obligations());
        if (!answers.keySet().equals(asked)) {
            throw new IllegalStateException(
                    "the obligations this run was asked for and the ones it answered for are not"
                            + " the same: asked " + InOneOrder.of(asked)
                            + ", answered " + InOneOrder.of(answers.keySet()));
        }
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

    /** Every answer, in the plan's own order. */
    public List<GenerationAnswer> inPlanOrder() {
        return plan.obligations().stream().map(answers::get).toList();
    }

    /** What became of each thing asked for, written in one order — see {@link InOneOrder}. */
    @Override
    public String toString() {
        return "answers " + InOneOrder.of(inPlanOrder());
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
        return at(new GenerationObligation.Arm(owed));
    }

    /**
     * The same, asked at one of the places a run through the arm is recorded.
     *
     * <p>For a reader holding an occurrence rather than the arm — a finding names one site of the
     * arm it is about, and what the search was asked for is the arm and every splice of it. Asked
     * with the site's own probe as though it were the whole key, such a reader found nothing
     * whenever the arm stood in the body more than once. Which arm the place belongs to is the
     * plan's answer, and the plan holds at most one arm at any place.
     */
    public ArmDisposition at(ArmProbe probe) {
        GenerationObligation.Arm owed = plan.armAt(probe);
        return owed == null ? null : at(owed);
    }

    private ArmDisposition at(GenerationObligation.Arm owed) {
        return answers.get(owed)
                instanceof GenerationAnswer.Arm(var _, var disposition) ? disposition : null;
    }
}
