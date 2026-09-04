package souther.compiler.values;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Which values one position admits, said as what it is rather than built as it is read.
 *
 * <p>The rules about a position are read one at a time and what they leave is one set, and those
 * two facts used to be the same walk: every conjunct met the last, so the set a position finally
 * admitted was a side effect of the order the clause put its parts in. Three things followed from
 * that and none of them was about the values. What was charged was what each step happened to
 * produce; which step was refused turned on which operands arrived together; and a refusal was
 * blamed on whatever rule was in hand when the allowance ran out.
 *
 * <p>So the reading says what the position admits and nothing else. What is here is a description —
 * the sets the rules name, met and joined the way the clause states them — and it is turned into a
 * {@link ValueSet} once, by something with an allowance to spend ({@link Sets}). Source order is
 * gone by then: two clauses that state the same thing in a different order are the same plan.
 *
 * <p><b>Normalised where it is made.</b> A meet of meets is one meet, {@link #ANY} met with
 * something is that something, a set stated twice is stated once, and two finite sets meet by
 * arithmetic that costs nothing. What is left after that is what actually has to be built, and
 * everything downstream — how it is planned, what it costs, whether it is refused — is a function
 * of it. A plan that kept the shape the author wrote would make the answer turn on the writing
 * again, one step further along.
 *
 * <p>{@link ValueSet} is not this and never becomes it. A set is exact, and what a reader asks of
 * one is answered by looking; this is what is asked for before there is a set to look at.
 */
public sealed interface AdmittedPlan {

    /** Every value there is, which is what a position no rule reached admits. */
    AdmittedPlan ANY = new Everything();

    /** Nothing at all, which is what refuses a declaration. */
    AdmittedPlan NONE = new Nothing();

    /**
     * The written things this plan asks machines for, which is where a refusal is answered from.
     *
     * <p>Every leaf that names one, and the compositions name none: what a meet of two patterns
     * asks for is what each of them asks for, and a refusal happens at one of them. Asked of the
     * plan rather than kept beside it, so a plan put together out of others carries what its parts
     * ask without anybody adding them up.
     */
    default java.util.Set<AuthoredOccurrence> asked() {
        java.util.Set<AuthoredOccurrence> out =
                java.util.Collections.newSetFromMap(new java.util.IdentityHashMap<>());
        switch (this) {
            case Everything _, Nothing _, Of _ -> { }
            case Pattern it -> out.add(it.occurrence());
            case Both it -> it.parts().forEach(each -> out.addAll(each.asked()));
            case Either it -> it.parts().forEach(each -> out.addAll(each.asked()));
        }
        return out;
    }

    /** Every value, as a plan. */
    record Everything() implements AdmittedPlan {}

    /** No value, as a plan. */
    record Nothing() implements AdmittedPlan {}

    /**
     * A set one rule says the position admits, worked out already.
     *
     * <p>The values an equality names, the values a denial leaves, and a set some other reading
     * arrived at and handed on. What is here has been built: whoever made it paid for it, and
     * asking what it holds asks for nothing more.
     */
    record Of(ValueSet set) implements AdmittedPlan {

        public Of {
            if (set == null || set.isAny() || set.isEmpty()) {
                throw new IllegalArgumentException(
                        "everything and nothing are said as themselves, not as a set of their own");
            }
        }

        /** Whether putting this together with something costs nothing, which is what the values a
         *  rule wrote out do. A language is the other kind. */
        boolean isFree() {
            return !(set instanceof ValueSet.Matching);
        }
    }

    /**
     * The strings a pattern accepts, named rather than made.
     *
     * <p>A machine, and it is not built here. What it costs to build is what this plan exists to
     * arrange — a pattern met with three written strings is a question about three strings, and
     * building the pattern to find that out is the spending the arrangement was for. So the leaf is
     * the pattern as written, and whether a machine is ever made of it is settled by what the plan
     * comes to and by what the position has left ({@link Realizer}).
     *
     * <p>Named by how it is written and not by what it accepts, for the same reason: two spellings
     * of one language are told apart by building both, which is the question being deferred. So
     * they are two leaves, which is also what they cost.
     *
     * @param occurrence the written place that asked for it. A machine is refused where it is made,
     *                   under the allowance of the position it is being built for — and every rule
     *                   reaching that position pays into the same allowance, so the position cannot
     *                   say which of them asked. Carried from where the asking is written, a refusal
     *                   names the pattern somebody wrote instead of every rule that mentions the
     *                   place it was written about
     * @param plan what would be built, which is the pattern a rule stated or every string less the
     *             pattern a rule denied
     */
    record Pattern(souther.compiler.values.AuthoredOccurrence occurrence,
                   souther.compiler.regex.PatternPlan plan) implements AdmittedPlan {

        public Pattern {
            if (occurrence == null) {
                throw new IllegalArgumentException(
                        "a pattern leaf is written somewhere, and says where");
            }
            if (plan == null) {
                throw new IllegalArgumentException("a pattern leaf names some pattern");
            }
        }
    }

    /**
     * What all of these admit, which is what rules stated together leave.
     *
     * <p>A set of parts and not a pair, because a meet is one connective however it was bracketed.
     * Two of them and more: {@link #meeting} refuses to make one of nought or one, since those are
     * every value and that one part.
     */
    record Both(Set<AdmittedPlan> parts) implements AdmittedPlan {

        public Both {
            parts = held(parts, "met");
        }
    }

    /** What any of these admits, which is what alternatives leave. */
    record Either(Set<AdmittedPlan> parts) implements AdmittedPlan {

        public Either {
            parts = held(parts, "joined");
        }
    }

    /**
     * The parts, in the order a plan holds parts in.
     *
     * <p>Sorted by what each of them is ({@link PlanOrder}) rather than kept as they arrived. A set
     * is equal to a set however either was filled, so two clauses stating the same rules the other
     * way round are one plan already — but a set filled in two orders is walked in two orders, and
     * whoever works the plan out does one thing before another. Held in an order the plan itself
     * decides, what is built first is the same for the same plan, and so is what it costs.
     */
    private static Set<AdmittedPlan> held(Set<AdmittedPlan> parts, String how) {
        if (parts == null || parts.size() < 2) {
            throw new IllegalArgumentException(
                    "a plan of one part is that part, so nothing here is " + how + " alone");
        }
        List<AdmittedPlan> order = new ArrayList<>(parts);
        order.sort(java.util.Comparator.comparing(PlanOrder::of));
        return Collections.unmodifiableSet(new LinkedHashSet<>(order));
    }

    /** The plan that is one set already known. */
    static AdmittedPlan of(ValueSet set) {
        if (set.isAny()) {
            return ANY;
        }
        return set.isEmpty() ? NONE : new Of(set);
    }

    /**
     * What all of them admit, normalised.
     *
     * <p>Flattened, since a meet of meets is one meet; every value dropped, since it narrows
     * nothing; nothing kept whole, since a meet with it is nothing; and each part once, since a
     * rule stated twice says it once. What is left is the meet that actually has to be built.
     *
     * <p>Written sets are met with each other here, because that costs nothing and leaves less to
     * build. The result is one written set among the parts, wherever the rules wrote any.
     */
    static AdmittedPlan meeting(List<AdmittedPlan> parts) {
        Set<AdmittedPlan> out = new LinkedHashSet<>();
        ValueSet written = null;
        for (AdmittedPlan each : flattened(parts, true)) {
            switch (each) {
                case Nothing _ -> {
                    return NONE;
                }
                case Everything _ -> { }
                // Two sets the rules wrote out are met here, since that costs nothing and leaves
                // less to build. A language is not folded in: putting one together with anything is
                // a machine, and where that happens is under an allowance.
                case Of it when it.isFree() -> written = written == null ? it.set()
                        : Sets.metPlainly(written, it.set());
                default -> out.add(each);
            }
        }
        if (written != null) {
            if (written.isEmpty()) {
                return NONE;
            }
            if (!written.isAny()) {
                out.add(new Of(written));
            }
        }
        return one(out, true);
    }

    /** What any of them admits, normalised the same way and the other way round. */
    static AdmittedPlan joining(List<AdmittedPlan> parts) {
        Set<AdmittedPlan> out = new LinkedHashSet<>();
        ValueSet written = null;
        for (AdmittedPlan each : flattened(parts, false)) {
            switch (each) {
                case Everything _ -> {
                    return ANY;
                }
                case Nothing _ -> { }
                case Of it when it.isFree() -> written = written == null ? it.set()
                        : Sets.joinedPlainly(written, it.set());
                default -> out.add(each);
            }
        }
        if (written != null) {
            if (written.isAny()) {
                return ANY;
            }
            if (!written.isEmpty()) {
                out.add(new Of(written));
            }
        }
        return one(out, false);
    }

    /** The parts of a plan of this connective, its own parts taken out of it. */
    private static List<AdmittedPlan> flattened(List<AdmittedPlan> parts, boolean met) {
        List<AdmittedPlan> out = new ArrayList<>();
        for (AdmittedPlan each : parts) {
            if (met && each instanceof Both it) {
                out.addAll(it.parts());
            } else if (!met && each instanceof Either it) {
                out.addAll(it.parts());
            } else {
                out.add(each);
            }
        }
        return out;
    }

    private static AdmittedPlan one(Set<AdmittedPlan> parts, boolean met) {
        if (parts.isEmpty()) {
            // Nothing was left to say: everything met with everything, or nothing joined with
            // nothing. Which of the two is the connective's own unit.
            return met ? ANY : NONE;
        }
        if (parts.size() == 1) {
            return parts.iterator().next();
        }
        return met ? new Both(parts) : new Either(parts);
    }
}
