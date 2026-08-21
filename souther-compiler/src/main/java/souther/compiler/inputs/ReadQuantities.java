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
 * <p>What {@link Quantities} says, made. The declarations reaching each parameter are read when one
 * of these is made, and not again: a question with several positions in it, and the same question
 * with some of them settled, are both answered from what that reading came to.
 */
final class ReadQuantities implements Quantities {

    private final Map<String, PlacedRules> byParameter;
    /** What the behavior takes, which is what a path of this input starts at. */
    private final Set<String> parameters;
    /** Every position that was read, by where it sits. What one of them was read to hold is what
     *  its own term runs between, and the reading that relates positions has a name for some of
     *  those terms and not for others. */
    private final Map<TermPath, Position> byPath;
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
                           Map<TermPath, Position> byPath, Map<NumericTerm, Count> fixed,
                           EmptyInput proved) {
        // In the order the behavior declares its parameters. A proof of emptiness names one of them
        // and a report is a document compared against the one written last time, so an order read
        // off a hash would move which parameter is named between runs.
        this.byParameter = java.util.Collections.unmodifiableMap(
                new LinkedHashMap<>(byParameter));
        this.parameters = Set.copyOf(parameters);
        this.byPath = Map.copyOf(byPath);
        this.fixed = Map.copyOf(fixed);
        this.proved = proved;
    }

    /** Before anything is fixed. */
    static ReadQuantities of(Map<String, PlacedRules> byParameter, Set<String> parameters,
                             Map<TermPath, Position> byPath) {
        return new ReadQuantities(byParameter, parameters, byPath, Map.of(), null);
    }

    /** Each parameter's rules read with what is fixed under it, once. */
    private Map<String, FieldDomains.Settled> conditioned() {
        Map<String, FieldDomains.Settled> read = conditioned;
        if (read == null) {
            Map<String, FieldDomains.Settled> made = new LinkedHashMap<>();
            byParameter.forEach((parameter, rules) ->
                    made.put(parameter, rules.given(under(parameter))));
            read = java.util.Collections.unmodifiableMap(made);
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
        // One term taken as itself, which is the arithmetic being the identity rather than a second
        // answer to the same question. It is also the only shape a position the arithmetic cannot
        // count is ever asked in — a form adds its terms together and two strings have no sum — so
        // this is where a floor written as a value rather than as a number survives at all.
        NumericTerm only = onlyTermOf(form);
        if (only != null) {
            // The relation still applies: what the rules leave one position under what is fixed is
            // the question a search asks between two steps, and it is the arithmetic that is the
            // identity here rather than the reading.
            return meeting(whereOneTermRuns(only), relatedTo(only));
        }
        // Added up out of parts, each holding as much as anything here can say about it, and never
        // met as two totals. Meeting does not distribute over addition — everything each term is on
        // its own, met against everything the relations leave the whole form, is wider than the sum
        // of the parts each met on its own — so one part nothing can be said about would take the
        // rules relating every other part down with it.
        return boundsOf(Reach.of(partsOf(form), Rational.of(form.constant()),
                part -> reachOf(part, form)));
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
        ReadQuantities wider = new ReadQuantities(byParameter, parameters, byPath, both, found);
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
    private static TermPath where(String parameter, souther.compiler.check.Emptiness why) {
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
                return new ReadQuantities(byParameter, parameters, byPath, fixed,
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

    /**
     * A part of a form that is answered on its own: the terms of one parameter the reading has a
     * coordinate for, or the ones it has none for.
     *
     * <p>The finest unit a relation survives in. What relates two positions is read of the value
     * they sit in, so a form reaching two parameters has a part in each; and within one, a
     * coordinate the reading never named is one no relation can be asked about, so what is known of
     * it is added beside the answer rather than taken into it.
     */
    private record Part(String parameter, boolean named) {}

    /** Which part of a form a term belongs to. */
    private Part partOf(NumericTerm term) {
        String parameter = term.path().head();
        FieldDomains.Settled rules = conditioned().get(parameter);
        return new Part(parameter, rules != null && rules.names(coordinateOf(term)));
    }

    /** The parts a form is made of, each contributing what it comes to once. */
    private Map<Part, Rational> partsOf(NumericDomain.LinearForm<NumericTerm> form) {
        Map<Part, Rational> parts = new LinkedHashMap<>();
        form.coefs().keySet().forEach(term -> parts.put(partOf(term), Rational.ONE));
        return parts;
    }

    /**
     * What one part of a form comes to: its terms on their own, and where the reading can be asked
     * about them, met with what its rules leave them together.
     *
     * <p>Met here and not at the end. What relates the positions is what the terms alone cannot say,
     * and what a term is on its own is what the relation need not have been told — held together at
     * the part, both survive whatever the part beside it came to.
     */
    private Reach reachOf(Part part, NumericDomain.LinearForm<NumericTerm> form) {
        Map<NumericTerm, Rational> mine = new LinkedHashMap<>();
        form.coefs().forEach((term, coef) -> {
            if (partOf(term).equals(part)) {
                mine.put(term, Rational.of(coef));
            }
        });
        Reach alone = Reach.of(mine, Rational.ZERO, this::atOneTerm);
        return part.named() ? tighter(alone, reachOf(relationallyOf(part.parameter(), form)))
                : alone;
    }

    /**
     * What the rules of one parameter leave the part of {@code form} they can be asked about.
     *
     * <p>The coordinates this reading names and no others. A form with one it never named is one
     * nothing can be said about as a whole, and asked that way the rules relating the coordinates
     * beside it are lost with it.
     */
    private NumericDomain.Bounds relationallyOf(String parameter,
                                                NumericDomain.LinearForm<NumericTerm> form) {
        FieldDomains.Settled rules = conditioned().get(parameter);
        if (rules == null) {
            return null;
        }
        Map<FieldDomains.Coordinate, BigDecimal> named = new LinkedHashMap<>();
        // And what each of those terms is on its own, put in rather than met on afterwards. The
        // rules relate the coordinates and a term guarantees things about itself that no clause
        // writes down; solved together they hold each other up, and taken apart and met the rule
        // over two of them says nothing as soon as a third is one the rules leave unbounded.
        Map<FieldDomains.Coordinate, NumericDomain.Bounds> ends = new LinkedHashMap<>();
        form.coefs().forEach((term, coef) -> {
            FieldDomains.Coordinate at = coordinateOf(term);
            if (term.path().head().equals(parameter) && rules.names(at)) {
                named.merge(at, coef, BigDecimal::add);
                ends.putIfAbsent(at, whereOneTermRuns(term));
            }
        });
        return rules.within(ends).boundsOf(named);
    }

    /** The coordinate of one term, in the words the rules of its parameter are read in. */
    private static FieldDomains.Coordinate coordinateOf(NumericTerm term) {
        return new FieldDomains.Coordinate(String.join(".", term.path().fields()),
                term instanceof NumericTerm.SizeOf);
    }

    /** The term a form is, where it is one term taken as itself, or null where it is arithmetic. */
    private static NumericTerm onlyTermOf(NumericDomain.LinearForm<NumericTerm> form) {
        if (form.coefs().size() != 1 || form.constant().signum() != 0) {
            return null;
        }
        Map.Entry<NumericTerm, BigDecimal> one = form.coefs().entrySet().iterator().next();
        return one.getValue().compareTo(BigDecimal.ONE) == 0 ? one.getKey() : null;
    }

    /**
     * What the rules relating this term to others leave it, or null where the reading cannot name
     * the coordinate.
     *
     * <p>The same question {@link #relationallyOf} asks of a form, of a form that is one term. Read
     * as bounds rather than as something to add up, because nothing is being added.
     */
    private NumericDomain.Bounds relatedTo(NumericTerm term) {
        return relationallyOf(term.path().head(), NumericDomain.LinearForm.atom(term));
    }

    /**
     * Where one term runs, as bounds rather than as something to add up.
     *
     * <p>Beside {@link #atOneTerm} and about the same three things. What it does not do is turn them
     * into numbers: a position ordered by its own values has ends that are values — a string stops
     * at {@code "A"} — and the arithmetic that adds terms together has no word for one.
     */
    private NumericDomain.Bounds whereOneTermRuns(NumericTerm term) {
        NumericDomain.Bounds runs = ownOf(term);
        NumericDomain.Bounds intrinsic = term.ownBounds();
        if (intrinsic != null) {
            runs = meeting(runs, intrinsic);
        }
        Count fixedAt = fixed.get(term);
        return fixedAt == null ? runs
                : meeting(runs, new NumericDomain.Bounds(Endpoint.inclusive(fixedAt),
                        Endpoint.inclusive(fixedAt)));
    }

    /** The tighter end on each side, where an absent bound is no bound and never the tighter. */
    private static NumericDomain.Bounds meeting(NumericDomain.Bounds one,
                                                NumericDomain.Bounds other) {
        if (one == null) {
            return other;
        }
        if (other == null) {
            return one;
        }
        return new NumericDomain.Bounds(Endpoint.lower(one.min(), other.min()),
                Endpoint.upper(one.max(), other.max()));
    }

    /**
     * What the position measured at this term was read to hold, or null where no position is
     * measured at it.
     *
     * <p>Which number a position is measured at is settled by the reading that made it, and a count
     * taken of a position the reading measured by its own value is a different quantity — answered
     * with the position's, a body measuring the length of a string would be told where the string
     * stops.
     */
    private NumericDomain.Bounds ownOf(NumericTerm term) {
        Position at = byPath.get(term.path());
        return at != null && term.equals(at.term()) ? at.numericDomain() : null;
    }

    /**
     * Where one term runs, from everything about that term and nothing about what it stands beside.
     *
     * <p>Three things and they are not one thing. A value the caller fixed it at is where it stands
     * whether or not any clause ever named that coordinate; what its own position was read to hold
     * is where its values stop, on whatever order it is measured — a text position has a floor and
     * no number for the arithmetic to relate; and what the term guarantees of itself is true of
     * every term of its kind, which is how a count is never negative without a clause saying so.
     *
     * <p>The position's answer only where the position is measured at this term. Which number a
     * position is measured at is settled by the reading that made it, and a count taken of a
     * position the reading measured by its own value is a different quantity — answered with the
     * position's, a body measuring the length of a string would be told where the string stops.
     */
    private Reach atOneTerm(NumericTerm term) {
        return reachOf(whereOneTermRuns(term));
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
