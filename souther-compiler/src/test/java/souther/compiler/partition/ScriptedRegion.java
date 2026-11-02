package souther.compiler.partition;

import souther.compiler.check.Emptiness;
import souther.compiler.inputs.EmptyInput;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.PlacesApart;
import souther.compiler.numeric.Rel;

import java.math.BigDecimal;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.BiFunction;
import java.util.function.Predicate;

/**
 * A region that answers as a script says, for tests about what a search does with the answers.
 *
 * <p>What a script gives is a function of what stands fixed in the region: whether the reading is
 * shown empty, where each position runs, and whether the reading of it is settled
 * ({@link SearchRegion#emptinessIsSettled}). Written as a function of the whole of what stands,
 * it can answer the regions on the way to an assignment one way and the assignment another, which
 * is what a reading that stopped short of the end does and what a region read from a model does not
 * do on the page. Every region a search narrows to shares the counts of the one it was handed.
 */
record ScriptedRegion(Counts counts, Map<NumericTerm, Place> standing, Script script)
        implements SearchRegion {

    static final NumericDomain.Bounds ZERO_TO_TEN = new NumericDomain.Bounds(
            Endpoint.inclusive(new Count(BigDecimal.ZERO)),
            Endpoint.inclusive(new Count(BigDecimal.TEN)));

    /** What the search reads and fixes. */
    static final class Counts {
        final AtomicInteger emptiness = new AtomicInteger();
        final AtomicInteger fixed = new AtomicInteger();
    }

    /**
     * What a region answers, as a function of what stands fixed in it.
     *
     * @param shownEmpty whether the reading is shown empty with these positions fixed
     * @param settled    what the region says of its reading of a whole assignment
     * @param runs       where a position runs, given what stands fixed; null where nowhere
     * @param narrowing  what the region says of its runs: that fixing a position only narrows them
     * @param unvouched  the numbers it has not been held for, which it answers no to whatever it
     *                   says of the rest
     */
    record Script(Predicate<Map<NumericTerm, Place>> shownEmpty, boolean settled,
                  BiFunction<Map<NumericTerm, Place>, NumericTerm, NumericDomain.Bounds> runs,
                  boolean narrowing, Predicate<NumericTerm> unvouched) {

        Script(Predicate<Map<NumericTerm, Place>> shownEmpty, boolean settled,
               BiFunction<Map<NumericTerm, Place>, NumericTerm, NumericDomain.Bounds> runs,
               boolean narrowing) {
            this(shownEmpty, settled, runs, narrowing, term -> false);
        }

        Script(Predicate<Map<NumericTerm, Place>> shownEmpty, boolean settled,
               BiFunction<Map<NumericTerm, Place>, NumericTerm, NumericDomain.Bounds> runs) {
            this(shownEmpty, settled, runs, true);
        }

        static Script refusingNothing() {
            return refusing(standing -> false);
        }

        static Script refusing(Predicate<Map<NumericTerm, Place>> shownEmpty) {
            return new Script(shownEmpty, true, (standing, term) -> ZERO_TO_TEN);
        }

        Script unsettled() {
            return new Script(shownEmpty, false, runs, narrowing, unvouched);
        }

        Script runningFrom(BiFunction<Map<NumericTerm, Place>, NumericTerm,
                NumericDomain.Bounds> narrower) {
            return new Script(shownEmpty, settled, narrower, narrowing, unvouched);
        }

        /** The runs a script gives, which this region does not say only narrow. */
        Script runningFromWithoutSayingTheyNarrow(BiFunction<Map<NumericTerm, Place>, NumericTerm,
                NumericDomain.Bounds> runs) {
            return new Script(shownEmpty, settled, runs, false, unvouched);
        }

        /** The same runs, said to only narrow. */
        Script sayingTheyNarrow() {
            return new Script(shownEmpty, settled, runs, true, unvouched);
        }

        /** The same, saying nothing for the numbers {@code unvouched} picks out. */
        Script notVouchingFor(Predicate<NumericTerm> unvouched) {
            return new Script(shownEmpty, settled, runs, narrowing, unvouched);
        }
    }

    static ScriptedRegion of(Script script) {
        return new ScriptedRegion(new Counts(), Map.of(), script);
    }

    @Override
    public Assumption assuming(LinearForm<NumericTerm> form, Rel rel) {
        return new Assumption.Taken(this);
    }

    @Override
    public SearchRegion assuming(NumericTerm.FromOnePosition term, Place at, Rel rel) {
        return this;
    }

    @Override
    public SearchRegion given(Map<NumericTerm, Place> fixed) {
        counts.fixed.incrementAndGet();
        Map<NumericTerm, Place> both = new LinkedHashMap<>(standing);
        both.putAll(fixed);
        return new ScriptedRegion(counts, both, script);
    }

    @Override
    public SearchRegion apartFrom(NumericTerm.FromOnePosition term, Place at) {
        return this;
    }

    @Override
    public PlacesApart apartAt(NumericTerm.FromOnePosition term) {
        return PlacesApart.NONE;
    }

    @Override
    public NumericDomain.FormProjection projectionOf(LinearForm<NumericTerm> form) {
        if (form.coefs().size() != 1) {
            return new NumericDomain.FormProjection.Within(ZERO_TO_TEN);
        }
        NumericTerm term = form.coefs().keySet().iterator().next();
        NumericDomain.Bounds runs = script.runs().apply(standing, term);
        return runs == null ? new NumericDomain.FormProjection.NothingIsLeft()
                : new NumericDomain.FormProjection.Within(runs);
    }

    @Override
    public Optional<EmptyInput> emptiness() {
        counts.emptiness.incrementAndGet();
        return script.shownEmpty().test(standing)
                ? Optional.of(new EmptyInput.ProvedByTheDeclarations(
                        new Emptiness.ConflictingRules()))
                : Optional.empty();
    }

    @Override
    public boolean emptinessIsSettled() {
        return script.settled();
    }

    @Override
    public boolean runsOnlyNarrowWhenFixed(Collection<? extends NumericTerm> terms) {
        return script.narrowing() && terms.stream().noneMatch(script.unvouched());
    }
}
