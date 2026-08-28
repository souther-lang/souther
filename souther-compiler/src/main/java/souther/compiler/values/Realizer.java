package souther.compiler.values;

import souther.compiler.regex.Meter;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What a position's plan comes to, built once and under an allowance.
 *
 * <p>The plan says which values the position admits and says it without an order
 * ({@link AdmittedPlan}); this turns it into the set. What that costs is counted where the states
 * are made ({@link Meter}), and where the allowance runs out what comes back is that it was not
 * built — never a smaller set, which would be this compiler answering a model with something it
 * made up because the truth was expensive.
 *
 * <p><b>The order the work is done in is this one's to choose, and it is chosen from the plan.</b>
 * A meet holding a set the rules wrote out is a meet whose answer is inside that set, so it is
 * settled by asking the written values and never by building anything — {@code [a-z]{300}} met with
 * {@code {"x"}} is a question about one string. Read in the order a clause happened to state it,
 * the same rules met the two patterns first and gave up on a product nobody needed. What is chosen
 * here is fixed by the plan and not by a heuristic that could change: a reader may work out what
 * this will do from what it is given.
 *
 * <p>Answers are kept, so a plan realized twice is realized once. Which is what lets a caller force
 * an answer early — to ask whether the position admits anything at all, say — without the position
 * paying twice for it, and what makes when it was asked not part of what it costs.
 */
final class Realizer {

    private final Meter meter;
    private final Map<AdmittedPlan, Realization> done = new LinkedHashMap<>();

    Realizer(Meter meter) {
        this.meter = meter;
    }

    /** What {@code plan} admits, worked out at most once however often it is asked for. */
    Realization of(AdmittedPlan plan) {
        Realization had = done.get(plan);
        if (had != null) {
            return had;
        }
        Realization made = built(plan);
        done.put(plan, made);
        return made;
    }

    private Realization built(AdmittedPlan plan) {
        return switch (plan) {
            case AdmittedPlan.Everything _ -> new Realization.Exact(ValueSet.ANY);
            case AdmittedPlan.Nothing _ -> new Realization.Exact(ValueSet.NONE);
            case AdmittedPlan.Of it -> new Realization.Exact(it.set());
            case AdmittedPlan.Both it -> met(it.parts());
            case AdmittedPlan.Either it -> joined(it.parts());
        };
    }

    /**
     * What all of them admit.
     *
     * <p>The written values first, wherever the plan holds any. What a meet with them leaves is a
     * subset of what they name, so the whole answer is settled by asking each of finitely many
     * values whether the rest admit it — and asking is free, whatever the rest are. This is the
     * cheap proof, and it is exact: nothing is approximated by taking it.
     *
     * <p>Everything else is met as languages, which is where the allowance goes.
     */
    private Realization met(java.util.Set<AdmittedPlan> parts) {
        List<AdmittedPlan> rest = new ArrayList<>();
        ValueSet written = null;
        for (AdmittedPlan each : parts) {
            if (each instanceof AdmittedPlan.Of it && it.isFree()) {
                written = written == null ? it.set() : Sets.metPlainly(written, it.set());
            } else {
                rest.add(each);
            }
        }
        // Only where the written values are named. A denial is every value but these, and which
        // ones it does admit is not a list to ask about — so a meet with one of those is built like
        // any other.
        if (written instanceof ValueSet.Finite named) {
            return keptOf(named, rest);
        }
        ValueSet out = written;
        for (AdmittedPlan each : rest) {
            Realization one = of(each);
            if (!(one instanceof Realization.Exact it)) {
                return one;
            }
            if (out == null) {
                out = it.set();
                continue;
            }
            Realization made = both(out, it.set());
            if (!(made instanceof Realization.Exact met)) {
                return made;
            }
            out = met.set();
        }
        return new Realization.Exact(out);
    }

    /**
     * Which of {@code written}'s values every one of {@code rest} admits.
     *
     * <p>Asked of each value, so nothing is built. A plan is realized to answer it — the parts of
     * {@code rest} are patterns and meets of them — but each answer is asked one string at a time,
     * and a language that was built for one value is kept for the next.
     */
    private Realization keptOf(ValueSet.Finite written, List<AdmittedPlan> rest) {
        java.util.Set<Value> left = new java.util.LinkedHashSet<>();
        for (Value value : written.values()) {
            boolean everywhere = true;
            for (AdmittedPlan each : rest) {
                Realization one = of(each);
                // A part this could not build is a part nobody knows the answer of, so neither is
                // the meet. Kept as admitted, the answer would be the values the parts this could
                // build agree on, said as though the rules had left them.
                if (!(one instanceof Realization.Exact it)) {
                    return one;
                }
                if (!it.set().has(value)) {
                    everywhere = false;
                    break;
                }
            }
            if (everywhere) {
                left.add(value);
            }
        }
        return new Realization.Exact(ValueSet.oneOf(left));
    }

    private Realization joined(java.util.Set<AdmittedPlan> parts) {
        ValueSet out = null;
        for (AdmittedPlan each : parts) {
            Realization one = of(each);
            if (!(one instanceof Realization.Exact it)) {
                return one;
            }
            if (out == null) {
                out = it.set();
                continue;
            }
            Realization made = either(out, it.set());
            if (!(made instanceof Realization.Exact joinedOne)) {
                return made;
            }
            out = joinedOne.set();
        }
        return new Realization.Exact(out);
    }

    private Realization both(ValueSet one, ValueSet other) {
        return outcome(Sets.metUnder(one, other, meter));
    }

    private Realization either(ValueSet one, ValueSet other) {
        return outcome(Sets.joinedUnder(one, other, meter));
    }

    private static Realization outcome(ValueSet made) {
        return made == null ? new Realization.TooCostly() : new Realization.Exact(made);
    }
}
