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
    private final Set<TermPath> paths;
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
    private volatile Map<String, PlacedRules> conditioned;

    private ReadQuantities(Map<String, PlacedRules> byParameter, Set<TermPath> paths,
                           Map<NumericTerm, Count> fixed, EmptyInput proved) {
        this.byParameter = Map.copyOf(byParameter);
        this.paths = Set.copyOf(paths);
        this.fixed = Map.copyOf(fixed);
        this.proved = proved;
    }

    /** Before anything is fixed. */
    static ReadQuantities of(Map<String, PlacedRules> byParameter, Set<TermPath> paths) {
        return new ReadQuantities(byParameter, paths, Map.of(), null);
    }

    /** Each parameter's rules read with what is fixed under it, once. */
    private Map<String, PlacedRules> conditioned() {
        Map<String, PlacedRules> read = conditioned;
        if (read == null) {
            Map<String, PlacedRules> made = new LinkedHashMap<>();
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
        ReadQuantities wider = new ReadQuantities(byParameter, paths, both, found);
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
        for (Map.Entry<String, PlacedRules> each : conditioned().entrySet()) {
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
     * <p>The proof the declarations hold, translated onto this input's paths. Where it names a field
     * of the value, the path it names is that value's own and the caller's is the parameter and the
     * field together.
     */
    private Optional<EmptyInput> holdsNothing(String parameter, PlacedRules rules) {
        return rules.bounds().holdsNothing().map(_ -> at(TermPath.of(parameter),
                new EmptyInput.ProvedByTheDeclarationsReading()));
    }

    /** An emptiness said to sit at {@code path}. */
    private static EmptyInput at(TermPath path, EmptyInput under) {
        return new EmptyInput.At(path, under);
    }

    /**
     * Whether each value just fixed is one its own position runs to.
     *
     * <p>Asked against what the position runs between, which takes in what the term guarantees of
     * itself. Sound whatever else is true: a value outside an over-approximation is outside the
     * rules, so this proves emptiness and never supposes it.
     */
    private ReadQuantities provingWhatIsFixedIsReachable(Map<NumericTerm, Count> just) {
        if (proved != null) {
            return this;   // the first proof stands, and this would be a second account of it
        }
        for (Map.Entry<NumericTerm, Count> each : just.entrySet()) {
            NumericDomain.Bounds runs = runsBetween(each.getKey());
            if (runs != null && !runs.admits(each.getValue())) {
                return new ReadQuantities(byParameter, paths, fixed,
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
     * The term, where its path is one of this input's.
     *
     * <p>Asked of the path and not of the terms the declarations named. Which numbers a position is
     * measured at is not settled by that reading alone — a bare list nothing bounds becomes an axis
     * about its length where a body measures it — and such a term is this input's as much as any
     * other. A term at a path this input does not have is a caller's mistake: answered as an
     * emptiness it would be a bug wearing the words of a contradiction in the model, and answered as
     * unbounded it would be one wearing the words of a model that says nothing.
     */
    private NumericTerm held(NumericTerm term) {
        if (!paths.contains(term.path())) {
            throw new IllegalArgumentException(
                    "`" + term.path() + "` is not a position of this input, so there is nothing"
                            + " here to answer about " + term);
        }
        return term;
    }

    /** What is fixed under one parameter, named the way that parameter's own rules name it. */
    private Map<String, Count> under(String parameter) {
        Map<String, Count> out = new LinkedHashMap<>();
        fixed.forEach((term, at) -> {
            // The value's own positions, and only the numbers among them. A count taken of a
            // position is not a position the declarations settle, so fixing one narrows nothing
            // there — which is less than the caller said and is the safe direction.
            if (term.path().head().equals(parameter) && term instanceof NumericTerm.ValueOf) {
                out.put(String.join(".", term.path().fields()), at);
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
        PlacedRules rules = conditioned().get(parameter);
        return rules == null ? Reach.ANYWHERE
                : reachOf(rules.bounds().boundsOf(partOf(parameter, form)));
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
