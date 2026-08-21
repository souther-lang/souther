package souther.compiler.inputs;

import souther.compiler.check.FieldDomains;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rational;
import souther.compiler.numeric.RationalCut;
import souther.compiler.numeric.Reach;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * The one reading of a behavior's input, asked about a quantity over several of its positions.
 *
 * <p>What {@link Quantities} says, made. Nothing is read here that {@link InputDomain} did not
 * already read: the declarations reaching each parameter were read once, and this asks them a
 * question with several positions in it instead of one.
 */
final class ReadQuantities implements Quantities {

    private final Map<String, PlacedRules> byParameter;
    /** What the behavior takes, which is what a path of this input starts at. */
    private final Set<String> parameters;
    private final Map<NumericTerm, Count> fixed;
    private final EmptyInput proved;
    /**
     * The rules read with everything fixed, worked out when something is asked and not before.
     *
     * <p>One reading per parameter and not one per question. A search asks where a position runs and
     * whether anything is left of the same refinement, and reading the declarations once per
     * question would read them twice a step. Held here rather than shared, since what it is a
     * reading of is what this refinement fixed.
     */
    private volatile Map<String, FieldDomains.Settled> conditioned;

    private ReadQuantities(Map<String, PlacedRules> byParameter, Set<String> parameters,
                           Map<NumericTerm, Count> fixed, EmptyInput proved) {
        this.byParameter = Map.copyOf(byParameter);
        this.parameters = Set.copyOf(parameters);
        this.fixed = Map.copyOf(fixed);
        this.proved = proved;
    }

    /** Before anything is fixed. */
    static ReadQuantities of(Map<String, PlacedRules> byParameter, Set<String> parameters) {
        return new ReadQuantities(byParameter, parameters, Map.of(), null);
    }

    /** Each parameter's rules read with what is fixed under it, once. */
    private Map<String, FieldDomains.Settled> conditioned() {
        Map<String, FieldDomains.Settled> read = conditioned;
        if (read == null) {
            Map<String, FieldDomains.Settled> made = new LinkedHashMap<>();
            byParameter.forEach((parameter, rules) ->
                    made.put(parameter, rules.given(under(parameter))));
            read = Map.copyOf(made);
            conditioned = read;
        }
        return read;
    }

    @Override
    public NumericDomain.Bounds runsBetween(NumericDomain.LinearForm<NumericTerm> form) {
        if (form.coefs().isEmpty()) {
            return null;
        }
        form.coefs().keySet().forEach(this::held);
        // What the term guarantees of itself, which the declarations need not have been told. A size
        // is never negative and no clause writes that down, so a reading of the clauses alone finds
        // nothing wrong with a form that runs below zero.
        Reach intrinsic = Reach.of(weighed(form), Rational.of(form.constant()),
                term -> reachOf(term.ownBounds()));
        // And what the rules leave it. One parameter at a time, because a parameter's rules are the
        // only ones that reach its positions: the part of the form over each is solved against that
        // parameter's rules, and the answers are added. The parts stay forms — added position by
        // position, the relation each part carries is the thing that would be lost.
        Reach related = Reach.of(byParameter(form), Rational.of(form.constant()),
                parameter -> relationally(parameter, form));
        return boundsOf(tighter(intrinsic, related));
    }

    @Override
    public Quantities given(Map<NumericTerm, Count> more) {
        if (more.isEmpty()) {
            return this;
        }
        Map<NumericTerm, Count> both = new LinkedHashMap<>(fixed);
        EmptyInput found = proved;
        for (Map.Entry<NumericTerm, Count> each : more.entrySet()) {
            NumericTerm term = held(each.getKey());
            Count at = each.getValue();
            Count had = both.put(term, at);
            // A position holds one value, so fixing it twice fixes it at nothing. Proved without
            // reading anything: what contradicts is the pair, and the rules were never asked.
            if (had != null && !had.equals(at)) {
                found = first(found, new EmptyInput.TwoValuesAtOnePosition(term, had, at));
            }
        }
        ReadQuantities wider = new ReadQuantities(byParameter, parameters, both, found);
        return wider.provingWhatIsFixedIsReachable(more);
    }

    /**
     * Why nothing is left, or empty where nothing proved it.
     *
     * <p>Read off what is held rather than worked out again per caller. Which route proved it — a
     * pair of assignments that cannot both stand, a value outside where its own position runs, or
     * the declarations read with everything fixed — is not a distinction anybody here may act on: a
     * caller that could tell them apart would be reading how the question was asked rather than what
     * the model says.
     */
    @Override
    public Optional<EmptyInput> emptiness() {
        if (proved != null) {
            return Optional.of(proved);
        }
        for (Map.Entry<String, FieldDomains.Settled> each : conditioned().entrySet()) {
            Optional<EmptyInput> here = holdsNothing(each.getKey(), each.getValue());
            if (here.isPresent()) {
                return here;
            }
        }
        return Optional.empty();
    }

    /**
     * The same, of one parameter's rules read with whatever is fixed under it.
     *
     * <p>The proof the declarations hold, said in this input's words. Where it names a position, the
     * path it names is that value's own — {@code x} for a field of the record the clause was written
     * on — and the caller's is the parameter and that path together. Left in the declaration's
     * words, a report would name a field of nothing; said as the parameter alone, it would name the
     * whole of what the behavior takes for a contradiction at one field of it.
     *
     * <p>One step and no further. A proof names one place once, so what sits under the step is not
     * another path of this value; what it can be is a proof about some other value, whose places are
     * that value's own and are not this input's to spell. So the where is carried across and the why
     * stays where it was proved.
     */
    private Optional<EmptyInput> holdsNothing(String parameter, FieldDomains.Settled rules) {
        return rules.holdsNothing().map(why -> at(where(parameter, why),
                new EmptyInput.ProvedByTheDeclarationsReading()));
    }

    /** The dot a path's steps are joined by, which is how one is taken apart again. */
    private static final java.util.regex.Pattern STEPS = java.util.regex.Pattern.compile("\\.");

    /** Where in this input the proof sits: the parameter, and the position under it the proof names
     *  where it names one. */
    static TermPath where(String parameter, souther.compiler.check.Emptiness why) {
        TermPath at = TermPath.of(parameter);
        if (!(why instanceof souther.compiler.check.Emptiness.AtAField field)
                || field.path().isEmpty()) {
            return at;
        }
        // Taken apart the way it was put together, and keeping what is between two dots even where
        // there is nothing there: a path is a list of steps joined by a dot, so a reading that drops
        // an empty step would answer about a different position than the one named.
        for (String step : STEPS.split(field.path(), -1)) {
            at = at.then(step);
        }
        return at;
    }

    /** An emptiness said to sit at {@code path}. */
    private static EmptyInput at(TermPath path, EmptyInput under) {
        return new EmptyInput.At(path, under);
    }

    /**
     * Whether each value just fixed is one the term itself can take.
     *
     * <p>Against what the term guarantees of its own values and against nothing else, which is what
     * makes this the whole of what fixing can settle without reading anything. A count is never
     * negative and no clause writes that down, so this is the only thing that refuses a count fixed
     * below none — and everything the declarations refuse is theirs to refuse, where they are read.
     *
     * <p>Not asked of what the rules leave the position, which is the same question one moment
     * later: the reading with this very value settled in it either pins the position to it or holds
     * nothing at all, so a check against that could never fail and would read the declarations to
     * find out.
     */
    private ReadQuantities provingWhatIsFixedIsReachable(Map<NumericTerm, Count> just) {
        if (proved != null) {
            return this;   // the first proof stands, and this would be a second account of it
        }
        for (Map.Entry<NumericTerm, Count> each : just.entrySet()) {
            NumericDomain.Bounds own = each.getKey().ownBounds();
            if (own != null && !own.admits(each.getValue())) {
                return new ReadQuantities(byParameter, parameters, fixed,
                        at(each.getKey().path(), new EmptyInput.OutsideWhereThePositionRuns(
                                each.getKey(), each.getValue())));
            }
        }
        return this;
    }

    /** The first proof found stands. A second is another account of an input already known to hold
     *  nothing rather than a further thing wrong with it. */
    private static EmptyInput first(EmptyInput had, EmptyInput found) {
        return had != null ? had : found;
    }

    /**
     * The term, where what it sits under is something this behavior takes.
     *
     * <p><b>Owned is not the same as known about.</b> The walk that reads an input's positions stops
     * two levels down, where a report stops being about anything an author would call one input, and
     * nothing stops a rule from naming what is under that. A term at such a path is this input's and
     * is answered for — with whatever the term guarantees of itself and nothing the declarations
     * relate it to, because the reading has no position there for a relation to be about. Refused
     * instead, an ordinary rule naming a field of a field of a field stopped a measurement rather
     * than being measured.
     *
     * <p>What is refused is a term under something this behavior does not take, which no reading of
     * this input could ever have an answer for. Answered as an emptiness it would be a bug wearing
     * the words of a contradiction in the model; answered as unbounded it would be one wearing the
     * words of a model that says nothing.
     *
     * <p>Whether the path names a field the type actually has is settled where the term is made.
     * What arrives here is a term some reading of an expression produced, and this neither checks
     * nor could check it: a path is a location and the declarations are what say what is at one.
     */
    private NumericTerm held(NumericTerm term) {
        if (!parameters.contains(term.path().head())) {
            throw new IllegalArgumentException(
                    "`" + term.path() + "` is under nothing this behavior takes, so there is"
                            + " nothing here to answer about " + term);
        }
        return term;
    }

    /** What is fixed under one parameter, named the way that parameter's own rules name it. */
    private Map<FieldDomains.Coordinate, Count> under(String parameter) {
        Map<FieldDomains.Coordinate, Count> out = new LinkedHashMap<>();
        fixed.forEach((term, at) -> {
            // Which number of the position was settled, and not only which position. A count taken
            // of a position is a coordinate of its own, and a fixing that named only the value left
            // a rule over two counts unconditioned while the same rule was read whole when the
            // counts were asked about.
            if (term.path().head().equals(parameter)) {
                out.put(new FieldDomains.Coordinate(String.join(".", term.path().fields()),
                        term instanceof NumericTerm.SizeOf), at);
            }
        });
        return out;
    }

    /** Which parameters the form reaches, each contributing its own part once. */
    private static Map<String, Rational> byParameter(
            NumericDomain.LinearForm<NumericTerm> form) {
        Map<String, Rational> parts = new LinkedHashMap<>();
        form.coefs().keySet().forEach(term -> parts.put(term.path().head(), Rational.ONE));
        return parts;
    }

    /** What one parameter's rules leave its part of the form, solved as a form. */
    private Reach relationally(String parameter, NumericDomain.LinearForm<NumericTerm> form) {
        FieldDomains.Settled rules = conditioned().get(parameter);
        return rules == null ? Reach.ANYWHERE
                : reachOf(rules.boundsOf(partOf(parameter, form)));
    }

    /** That part of the form, in the words the parameter's own rules are read in. */
    private static Map<FieldDomains.Coordinate, BigDecimal> partOf(
            String parameter, NumericDomain.LinearForm<NumericTerm> form) {
        Map<FieldDomains.Coordinate, BigDecimal> out = new LinkedHashMap<>();
        form.coefs().forEach((term, coef) -> {
            if (term.path().head().equals(parameter)) {
                out.merge(new FieldDomains.Coordinate(String.join(".", term.path().fields()),
                        term instanceof NumericTerm.SizeOf), coef, BigDecimal::add);
            }
        });
        return out;
    }

    private static Map<NumericTerm, Rational> weighed(NumericDomain.LinearForm<NumericTerm> form) {
        Map<NumericTerm, Rational> out = new LinkedHashMap<>();
        form.coefs().forEach((term, coef) -> out.put(term, Rational.of(coef)));
        return out;
    }

    private static Reach reachOf(NumericDomain.Bounds bounds) {
        return bounds == null ? Reach.ANYWHERE
                : Reach.between(asCut(bounds.min()), asCut(bounds.max()));
    }

    private static RationalCut asCut(Endpoint end) {
        return end == null || !(end.at() instanceof Count at) ? null
                : new RationalCut(Rational.of(at.at()), end.inclusive());
    }

    private static Reach tighter(Reach one, Reach other) {
        return new Reach(RationalCut.tighterLower(one.least(), other.least()),
                RationalCut.tighterUpper(one.most(), other.most()));
    }

    private static NumericDomain.Bounds boundsOf(Reach runs) {
        if (runs.least() == null && runs.most() == null) {
            return null;
        }
        return new NumericDomain.Bounds(written(runs.least(), false), written(runs.most(), true));
    }

    private static Endpoint written(RationalCut cut, boolean upper) {
        if (cut == null) {
            return null;
        }
        BigDecimal exactly = cut.at().asWrittenDecimal();
        if (exactly != null) {
            return new Endpoint(new Count(exactly), cut.inclusive());
        }
        // Rounded the way that widens, so what is handed over admits everything the rules admit and
        // a hair besides. Refusing a value the rules leave is the failure nothing downstream sees.
        return new Endpoint(new Count(cut.at().asDecimal(
                upper ? java.math.RoundingMode.CEILING : java.math.RoundingMode.FLOOR,
                DIGITS_WHEN_IT_IS_NOT_A_DECIMAL)), true);
    }

    /** How far a derived end is written out where the division that makes it does not end. Any
     *  number of them is sound while the rounding goes outward. */
    private static final int DIGITS_WHEN_IT_IS_NOT_A_DECIMAL = 32;
}
