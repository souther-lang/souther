package souther.compiler.inputs;

import souther.compiler.check.FieldDomains;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rational;
import souther.compiler.numeric.RationalCut;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.List;
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

    private final Map<TermPath, PlacedRules> byRoot;
    /** What says how the values of a position are spaced, which the arithmetic needs of every
     *  number it is told a bound on. Held rather than asked for per question: the reading of an
     *  input is what a caller has, and where a position's values step is a fact about its type. */
    private final souther.compiler.check.Symbols symbols;
    /** What the behavior takes, which is what a path of this input starts at. */
    private final Set<TermPath> roots;
    /** Every position that was read, by where it sits. What one of them was read to hold is what
     *  its own term runs between, and the reading that relates positions has a name for some of
     *  those terms and not for others. */
    private final Map<TermPath, Position> byPath;
    /**
     * What stands where a path names, as the reading that made this has it.
     *
     * <p>Beside {@link #byPath} and not the same question. That one answers whether this reading
     * measured a position, which is what a term's own bounds are read off; this one answers what a
     * path stands at whether or not the reading stopped above it, which is what an order follows
     * from. Answered here off the positions alone, a rule naming a field every case of a sum
     * spreads would be told nothing stands where the language reads a value.
     *
     * <p>The resolution and not the walk. What is handed over is one question already answered, so
     * nothing here can reach the rest of the reading or ask it something else.
     */
    private final java.util.function.Function<TermPath, Type> typeAt;
    /**
     * The reading this was made from.
     *
     * <p>Held so that a caller handed both can be asked whether they are of one reading, and for
     * nothing else: two readings of two behaviors can have a parameter spelled the same way, and a
     * term made against one of them is answered by the other without either saying anything is
     * wrong. Nothing here reads it, and it is not reachable from outside this package.
     */
    private final InputDomain of;
    /**
     * What each term has been fixed at, as the least and the greatest of the values fixed there.
     *
     * <p>A pair and not a value, because what a caller settles has to accumulate the same way
     * whichever order it arrives in. Fixing one position twice is fixing it at nothing, and holding
     * the last value to arrive — or the first — would make which of the two a proof names depend on
     * the order the question was asked in. Where a term has been fixed once the two are the same.
     */
    private final Map<NumericTerm, Fixed> fixed;
    /**
     * What a caller has taken in about this input beyond what the declarations say.
     *
     * <p>Reached only through {@link SearchRegion}, which is what keeps a reading of the
     * declarations from acquiring one. Kept as what was said and not as what it came to: taking in
     * accumulates, and what the whole of it leaves is worked out where everything else is.
     */
    private final List<Assumed> assumed;
    /**
     * The rules read with everything fixed, worked out when something is asked and not before.
     *
     * <p>One reading per value and not one per question. A search asks where a position runs and
     * whether anything is left of the same refinement, and reading the declarations once per
     * question would read them twice a step. Held here rather than shared, since what it is a
     * reading of is what this refinement fixed.
     */
    private volatile Map<TermPath, FieldDomains.Carried<InputAtom>> conditioned;
    /**
     * Every rule reaching this input, about this input's own subjects, in one place.
     *
     * <p>Not one reading per parameter with the answers added afterwards. Adding per-parameter
     * answers is the composition a rule spanning two parameters cannot survive, and where such a
     * rule comes from is not this layer's business — what is here is a constraint space over the
     * input, and where one parameter's positions run is a projection out of it rather than a
     * reading of its own.
     *
     * <p><b>The whole state and not the numbers of it.</b> Whether anything is left of this input is
     * one question, and this is the one thing that answers it: a per-parameter reading kept beside
     * this one could answer it too, over the same numbers renamed, and then which of two proofs is
     * written would be settled by the order they are asked in — with the weaker of them, the one
     * that cannot see across two parameters, asked first. The parameters supply rules here and
     * answer nothing.
     *
     * <p>Worked out when something is asked and kept, the same as {@link #conditioned}: it is a
     * reading of what this refinement fixed, so it belongs to this value and not to a shared table.
     */
    private volatile souther.compiler.check.ConstraintState<InputAtom> constraints;
    /** Where each position of the input sits, in the order the parameters and their positions are
     *  declared. What a proof of emptiness names a place out of. */
    private volatile java.util.SequencedMap<InputAtom, String> positions;

    /** One thing taken in about a form of this input's terms: {@code form rel 0}. */
    private record Assumed(NumericDomain.LinearForm<NumericTerm> form, NumericDomain.Rel rel) {}

    /** The values fixed at one term, kept as their least and greatest so that what was fixed does
     *  not depend on the order it arrived in. */
    private record Fixed(Count least, Count most) {

        Fixed and(Count also) {
            return new Fixed(least.compareTo(also) <= 0 ? least : also,
                    most.compareTo(also) >= 0 ? most : also);
        }

        boolean isOne() {
            return least.equals(most);
        }
    }

    private ReadQuantities(InputDomain of, Map<TermPath, PlacedRules> byRoot, Set<TermPath> roots,
                           Map<TermPath, Position> byPath,
                           java.util.function.Function<TermPath, Type> typeAt,
                           Map<NumericTerm, Fixed> fixed,
                           souther.compiler.check.Symbols symbols, List<Assumed> assumed) {
        this.of = of;
        this.symbols = symbols;
        this.typeAt = typeAt;
        this.assumed = List.copyOf(assumed);
        // In the order the behavior declares its parameters. A proof of emptiness names one of them
        // and a report is a document compared against the one written last time, so an order read
        // off a hash would move which parameter is named between runs.
        this.byRoot = java.util.Collections.unmodifiableMap(new LinkedHashMap<>(byRoot));
        this.roots = Set.copyOf(roots);
        this.byPath = Map.copyOf(byPath);
        // Kept in the order the fixings arrived, so that the order they are answered in is chosen
        // here rather than inherited. An immutable copy iterates in an order salted once per JVM
        // run, which is a fine order and not one anybody chose — read off it, which of two
        // contradictions a proof names would move between runs of the same compiler.
        this.fixed = java.util.Collections.unmodifiableMap(new LinkedHashMap<>(fixed));
    }

    /** Before anything is fixed. */
    static ReadQuantities of(InputDomain from, Map<TermPath, PlacedRules> byRoot,
                             Set<TermPath> roots,
                             Map<TermPath, Position> byPath,
                             java.util.function.Function<TermPath, Type> typeAt,
                             souther.compiler.check.Symbols symbols) {
        return new ReadQuantities(from, byRoot, roots, byPath, typeAt, Map.of(), symbols,
                List.of());
    }

    /** Whether {@code reading} is the one this was made from, which is what a caller handed both of
     *  them has to establish before it uses them together. */
    boolean isOf(InputDomain reading) {
        return of == reading;
    }

    /**
     * Both orders of {@code term}, from where the reading has its subject standing.
     *
     * <p>Carried into every refinement of this reading rather than answered against what is fixed:
     * what a term is measured on is a fact about where it sits, and fixing a position at a value
     * says nothing about the order that value is counted on.
     */
    @Override
    public TermOrders ordersOf(NumericTerm term) {
        // Refused for a term under nothing this behavior takes, the same as every other question
        // here. What an operation answers with follows from the operation alone where the type is
        // absent, so a term of another input comes back with an order on one end and nothing on the
        // other — an answer about no reading, wearing this one's name.
        held(term);
        return term.ordersAt(typeAt.apply(term.subjectPath()), symbols);
    }

    @Override
    public int mostHeldAt(PositionId at) {
        Position position = byPath.get(at.at());
        // Refused where this reading has no such position, the way a term under nothing this
        // behavior takes is refused. A coordinate a value is built at is spelled the same way and is
        // not one of these, and answered with "no rule bounds it" the reading would be saying
        // something about a place it has never been.
        if (position == null) {
            throw new IllegalArgumentException(
                    "`" + at + "` is no position of this input, so there is nothing here to say"
                            + " how many it holds");
        }
        // The position's own count, which is the one question here that names an arm — and it names
        // it because it is about that arm.
        if (!(position.term() instanceof NumericTerm.TakenOf taken)
                || !(taken.takenAs()
                        instanceof souther.compiler.semantics.TakenAs.HowManyItHolds)) {
            return Integer.MAX_VALUE;
        }
        // Asked of the rules when the question arrives rather than solved for every container as
        // the reading is made: what they leave a count moves with whatever else has been settled.
        NumericDomain.Bounds runs = runsBetween(position.term());
        return runs == null ? Integer.MAX_VALUE
                : souther.compiler.numeric.CountDomain.mostFrom(runs.max());
    }

    /**
     * The value {@code path} is a position of, or null where it is a position of nothing this
     * reading holds.
     *
     * <p>The nearest, which is the one whose clauses can name it: a field of a case is under the
     * parameter as well, and what the parameter's own rules say stops at the narrowing. Read as the
     * outermost, a clause of the sum would be asked about a position inside one of its cases.
     */
    private TermPath rootOf(TermPath path) {
        TermPath nearest = null;
        for (TermPath root : roots) {
            if (path.isAtOrUnder(root)
                    && (nearest == null || root.isAtOrUnder(nearest))) {
                nearest = root;
            }
        }
        return nearest;
    }

    /** Each parameter's rules read with what is fixed under it, once, under this input's names. */
    private Map<TermPath, FieldDomains.Carried<InputAtom>> conditioned() {
        Map<TermPath, FieldDomains.Carried<InputAtom>> read = conditioned;
        if (read == null) {
            Map<TermPath, FieldDomains.Carried<InputAtom>> made = new LinkedHashMap<>();
            byRoot.forEach((root, rules) -> made.put(root,
                    rules.given(under(root)).constraintsOver(
                            at -> called(root, at),
                            subject -> new InputAtom.Anonymous(root.toString(), subject))));
            read = java.util.Collections.unmodifiableMap(made);
            conditioned = read;
        }
        return read;
    }

    @Override
    public SearchRegion region() {
        return new ReadRegion(this);
    }

    /**
     * The same rules, with {@code form rel 0} taken in as well.
     *
     * <p>Reached only through {@link ReadRegion}, so what comes back is a region and never a reading
     * of the declarations. What is kept is the assertion and not what it came to: two of them said
     * in either order are the same two, and one said twice is one.
     *
     * <p>This value back where the arithmetic cannot take the assertion in — a form over a position
     * whose values it has no spacing for. Kept anyway, it would sit in the state as a rule about a
     * number nothing knows how to space, which {@link souther.compiler.numeric.NumericDomain#assume}
     * refuses outright; declined here, the region still holds everything that reaches the border,
     * which is the direction every reader of it depends on.
     */
    ReadQuantities assuming(NumericDomain.LinearForm<NumericTerm> form, NumericDomain.Rel rel) {
        if (form == null || form.coefs().isEmpty()) {
            return this;
        }
        for (NumericTerm term : form.coefs().keySet()) {
            held(term);
            if (spacingOf(constraints().numbers(), term, called(term)) == null) {
                return this;
            }
        }
        Assumed taking = new Assumed(form, rel);
        if (assumed.contains(taking)) {
            return this;
        }
        List<Assumed> both = new java.util.ArrayList<>(assumed);
        both.add(taking);
        return new ReadQuantities(of, byRoot, roots, byPath, typeAt, fixed, symbols, both);
    }

    /**
     * The rules of every parameter, renamed into this input's vocabulary and said together.
     *
     * <p>Renamed and not read again ({@link FieldDomains.Settled#constraintsOver}). What a rule says
     * is a relation between subjects, and it says the same thing whatever they are called — so what
     * reaches here is each parameter's reading, under names this input can spell, and a subject it
     * cannot spell under a name of its own so that the rules through it are not lost.
     *
     * <p>Said together, which is what makes this a constraint space rather than a product of them.
     * Two parameters are related by nothing the declarations say, so meeting their rules leaves
     * every answer where it was; what it does is leave somewhere for a rule that relates them to be
     * said at all.
     *
     * <p>And what each number is on its own goes in here rather than being met on afterwards.
     * Projecting does not distribute over meeting: a rule holding two numbers at one apiece says
     * nothing about a form that also names a third the rules leave unbounded, and met afterwards
     * against a floor this reading did have, the rule is gone.
     */
    private souther.compiler.check.ConstraintState<InputAtom> constraints() {
        souther.compiler.check.ConstraintState<InputAtom> read = constraints;
        if (read != null) {
            return read;
        }
        souther.compiler.check.ConstraintState<InputAtom> made =
                souther.compiler.check.ConstraintState.top();
        // What the values of this space cost to work out. One for the space and not one per
        // parameter: what each parameter was read under is the allowance of its own declaration,
        // and the set a position finally admits here is met out of all of them — so this is the
        // answer being built and this is where building it is charged.
        souther.compiler.values.Allowance<InputAtom> sets =
                souther.compiler.values.Allowance.ofAdmittedValues();
        for (FieldDomains.Carried<InputAtom> each : conditioned().values()) {
            made = made.meet(each.constraints().under(sets));
        }
        // And what the caller took in, onto the same rules rather than met against the answer
        // afterwards. A condition relating two positions says nothing about either of them alone,
        // so met afterwards it would be gone.
        for (Assumed each : assumed) {
            Map<InputAtom, souther.compiler.numeric.Granularity> spacing = new LinkedHashMap<>();
            for (NumericTerm term : each.form().coefs().keySet()) {
                souther.compiler.numeric.Granularity spaced =
                        spacingOf(made.numbers(), term, called(term));
                if (spaced == null) {
                    spacing = null;
                    break;
                }
                spacing.put(called(term), spaced);
            }
            if (spacing != null) {
                made = made.taking(over(each.form()), each.rel(), spacing);
            }
        }
        read = made;
        constraints = read;
        return read;
    }

    /**
     * Where each position of this input sits, in the order they are declared.
     *
     * <p>What a proof of emptiness names a place out of, so the order is the model's and not a
     * traversal's: the parameters in the order the behavior takes them, and the positions of each in
     * the order its value declares them. Read off a map salted once per run, which position a
     * refusal names would move between runs of the same compiler.
     *
     * <p>The parameter and the declaration's own path joined, because the two spellings are the same
     * place or the report names one nobody wrote. A field of the record a clause was written on is
     * {@code x} there and {@code p.x} here, and this is where it becomes the second.
     */
    private java.util.SequencedMap<InputAtom, String> positions() {
        java.util.SequencedMap<InputAtom, String> read = positions;
        if (read != null) {
            return read;
        }
        java.util.SequencedMap<InputAtom, String> made = new LinkedHashMap<>();
        conditioned().forEach((root, carried) -> carried.positions().forEach(
                // What a newtype wraps has no path of its own, so the place is the value itself.
                (atom, path) -> made.put(atom, FieldDomains.THE_VALUE.equals(path)
                        ? root.toString() : root + "." + path)));
        read = java.util.Collections.unmodifiableSequencedMap(made);
        positions = read;
        return read;
    }

    /** What this input calls the number at one of a value's coordinates. */
    private static InputAtom called(TermPath root, FieldDomains.Coordinate at) {
        return new InputAtom.Named(root.toString(), at.path(), at.kind());
    }

    /** The same, of a term this input holds. One number under one name whichever side it arrives
     *  from — the reading of a declaration, or a form a caller wrote. */
    private InputAtom.Named called(NumericTerm term) {
        TermPath root = rootOf(term.subjectPath());
        FieldDomains.Coordinate at = coordinateOf(root, term);
        return new InputAtom.Named(root.toString(), at.path(), at.kind());
    }

    /**
     * The rules with what one term is on its own taken in.
     *
     * <p>Three things, and none of them is a clause: a value the caller fixed it at, what the
     * position measured at it was read to hold, and what the term guarantees of itself. All three
     * are true whether or not any clause ever named the coordinate, and they are put onto the rules
     * rather than met against the answer so that they are solved together with the relations.
     *
     * <p>Ends that are not numbers are left out, because what is being added to is the arithmetic. A
     * position ordered by its own values has ends that are values — a string stops at {@code "A"} —
     * and that end survives where a form is one term taken as itself ({@link #runsBetween}), which
     * is the only shape such a position is ever asked in.
     */
    private souther.compiler.numeric.NumericDomain<InputAtom> holding(
            souther.compiler.numeric.NumericDomain<InputAtom> rules, NumericTerm term) {
        NumericDomain.Bounds runs = whereOneTermRuns(term);
        if (runs == null || (asCut(runs.min()) == null && asCut(runs.max()) == null)) {
            return rules;
        }
        InputAtom atom = called(term);
        souther.compiler.numeric.Granularity spaced = spacingOf(rules, term, atom);
        if (spaced == null) {
            return rules;
        }
        return rules.assuming(atom, numbersOf(runs), Map.of(atom, spaced));
    }

    /** A range with only the ends the arithmetic has a number for. */
    private static NumericDomain.Bounds numbersOf(NumericDomain.Bounds runs) {
        return new NumericDomain.Bounds(
                asCut(runs.min()) == null ? null : runs.min(),
                asCut(runs.max()) == null ? null : runs.max());
    }

    /**
     * How the values of one term are spaced.
     *
     * <p>What the rules already record about it where they record anything, and what its type says
     * where they do not. Asked of the rules first because that is where the two could disagree, and
     * one number spaced two ways is the naming and the typing disagreeing rather than something to
     * pick the safer of.
     *
     * <p>Null where nothing says. A bound may not be taken in on a number whose spacing is guessed —
     * a strict bound is either wrongly sharpened on it or silently left blunt — so what is not
     * known is left out, and what the rules leave is then wider rather than wrong.
     */
    private souther.compiler.numeric.Granularity spacingOf(
            souther.compiler.numeric.NumericDomain<InputAtom> rules, NumericTerm term,
            InputAtom atom) {
        souther.compiler.numeric.Granularity had = rules.spacingOf(atom);
        if (had != null) {
            return had;
        }
        if (symbols == null) {
            return null;
        }
        // The order this reading measures the term on, which is the same answer every other reader
        // of it gets. Worked out here from the positions alone, a term whose subject the reading
        // stopped above — a field every case of a sum spreads is one — was spaced by nothing while
        // the order was there to be had, and a count under more steps than the enumeration goes
        // down would lose the floor every count has.
        souther.compiler.check.Carrier carrier = ordersOf(term).answered();
        return carrier == null ? null : carrier.spacing();
    }

    @Override
    public NumericDomain.Bounds runsBetween(NumericDomain.LinearForm<NumericTerm> form) {
        if (form.coefs().isEmpty()) {
            return null;
        }
        form.coefs().keySet().forEach(this::held);
        // Projected out of the rules, which is one question with one answer. The rules of every
        // parameter are said together and what each number is on its own is said onto them, so what
        // a form runs between is read off that space rather than assembled out of per-parameter
        // answers — assembling is what a rule spanning two parameters cannot survive.
        souther.compiler.numeric.NumericDomain<InputAtom> rules = constraints().numbers();
        for (NumericTerm term : form.coefs().keySet()) {
            rules = holding(rules, term);
        }
        NumericDomain.Bounds projected = rules.boundsOf(over(form));
        // One term taken as itself, which is the arithmetic being the identity rather than a second
        // answer to the same question. It is also the only shape a position the arithmetic cannot
        // count is ever asked in — a form adds its terms together and two strings have no sum — so
        // this is where a floor written as a value rather than as a number survives at all.
        NumericTerm only = onlyTermOf(form);
        return only == null ? projected : meeting(projected, whereOneTermRuns(only));
    }

    /**
     * A form of this input's terms, as one over the numbers the rules are about.
     *
     * <p><b>Added and not overwritten, because this is a fold and not a renaming.</b> A term carries
     * which measure was written and a number does not, so two terms can be one number — and where a
     * form weighs both of them, what that number is weighed by is the two coefficients together.
     * Written as a renaming, {@code List.length(p.xs) + Set.size(p.xs)} would come back weighing
     * that count once, which is a form the caller did not write and a range that is not the one they
     * asked about.
     *
     * <p>The other way round from {@link souther.compiler.numeric.NumericDomain#over}, and the two
     * are not the same act. Carrying a rule across may not put two positions under one name — that
     * would say they are one number, which nobody said. Reading a caller's form may, because the
     * caller wrote two spellings of a number this input has one of.
     */
    private NumericDomain.LinearForm<InputAtom> over(
            NumericDomain.LinearForm<NumericTerm> form) {
        Map<InputAtom, BigDecimal> coefs = new LinkedHashMap<>();
        form.coefs().forEach((term, coef) -> coefs.merge(called(term), coef, BigDecimal::add));
        return new NumericDomain.LinearForm<>(form.constant(), coefs);
    }

    @Override
    public Quantities given(Map<NumericTerm, Count> more) {
        return fixing(more);
    }

    /**
     * The same, answered as this reading rather than as one of the faces it wears.
     *
     * <p>What refining hands back is the state, and {@link Quantities} and {@link SearchRegion} are
     * two ways of asking it. Typed by either of them, the other has to put back what it knows —
     * which is a cast, and a cast is a check the compiler is not doing. The two faces stay apart
     * because they answer different questions; what they refine is one thing and is typed as one.
     */
    ReadQuantities fixing(Map<NumericTerm, Count> more) {
        if (more.isEmpty()) {
            return this;
        }
        Map<NumericTerm, Fixed> both = new LinkedHashMap<>(fixed);
        for (Map.Entry<NumericTerm, Count> each : more.entrySet()) {
            NumericTerm term = held(each.getKey());
            both.merge(term, new Fixed(each.getValue(), each.getValue()),
                    (had, one) -> had.and(one.least()));
        }
        return new ReadQuantities(of, byRoot, roots, byPath, typeAt, both, symbols, assumed);
    }

    /**
     * Why nothing is left, or empty where nothing proved it.
     *
     * <p><b>Worked out from what is fixed, and not from how it came to be fixed.</b> Two positions
     * fixed at values neither can take are two contradictions, and which of them a caller hears
     * about is not something the model says — kept as the first one a fixing happened to meet, the
     * answer would carry the order the questions were asked in. So nothing is remembered along the
     * way: the same accumulation answers the same thing, whichever way round it was reached and
     * whether it arrived in one call or four.
     *
     * <p>Looked for in one order, which is a settled order and not a preference. A position fixed at
     * two values contradicts without anything being read; a value the term itself cannot take
     * contradicts against what the term guarantees; and what the declarations refuse is theirs to
     * refuse. The terms are taken in the order they are written down, so two contradictions of one
     * kind are told apart by where they sit rather than by when they were found.
     */
    @Override
    public Optional<EmptyInput> emptiness() {
        for (Map.Entry<NumericTerm, Fixed> each : inOrder()) {
            if (!each.getValue().isOne()) {
                return Optional.of(new EmptyInput.TwoValuesAtOnePosition(each.getKey(),
                        each.getValue().least(), each.getValue().most()));
            }
        }
        for (Map.Entry<NumericTerm, Fixed> each : inOrder()) {
            NumericDomain.Bounds own = each.getKey().intrinsicBounds();
            if (!own.admits(each.getValue().least())) {
                return Optional.of(new EmptyInput.OutsideWhereThePositionRuns(each.getKey(),
                        each.getValue().least()));
            }
        }
        // And what the rules leave once they are all said together, which is the one thing that
        // answers it. Every parameter's reading is in here, renamed, so there is nothing a
        // per-parameter reading could add — and a contradiction between two parameters, or between a
        // declaration and something a caller took in, can be seen nowhere else.
        return constraints().holdsNothing(positions()).map(EmptyInput.ProvedByTheRules::new);
    }

    /**
     * What is fixed, in the order the terms are written down.
     *
     * <p>Any order settled by the terms themselves would do; what may not decide it is the order the
     * fixings arrived in, which is the caller's business and not the model's.
     */
    private List<Map.Entry<NumericTerm, Fixed>> inOrder() {
        List<Map.Entry<NumericTerm, Fixed>> out = new java.util.ArrayList<>(fixed.entrySet());
        out.sort(java.util.Comparator.comparing(each -> each.getKey().toString()));
        return out;
    }

    /**
     * The term, where what it sits under is something this behavior takes.
     *
     * <p><b>Owned is not the same as known about.</b> The reading holds the positions the
     * enumeration found and the ones the measurement named, and nothing stops a rule from naming a
     * path outside both. A term at such a path is this input's and
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
        if (rootOf(term.subjectPath()) == null) {
            throw new IllegalArgumentException(
                    "`" + term.subjectPath() + "` is under nothing this behavior takes, so there is"
                            + " nothing here to answer about " + term);
        }
        return term;
    }

    /** What is fixed under one value, named the way that value's own rules name it. */
    private Map<FieldDomains.Coordinate, Count> under(TermPath root) {
        Map<FieldDomains.Coordinate, Count> out = new LinkedHashMap<>();
        fixed.forEach((term, at) -> {
            // Which number of the position was settled, and not only which position. A count taken
            // of a position is a coordinate of its own, and a fixing that named only the value left
            // a rule over two counts unconditioned while the same rule was read whole when the
            // counts were asked about.
            // Only where one value was fixed there. A position fixed at two settles nothing the
            // declarations could be told, and what it contradicts is said here rather than by them.
            if (root.equals(rootOf(term.subjectPath())) && at.isOne()) {
                out.put(coordinateOf(root, term), at.least());
            }
        });
        return out;
    }

    /** The coordinate of one term, in the words the rules of the value it is a position of are
     *  read in. */
    private static FieldDomains.Coordinate coordinateOf(TermPath root, NumericTerm term) {
        // Written with the steps inside a sequence in it, so two positions never come to one name.
        // No clause is written at such a name, so a lookup finds nothing — which is what a clause
        // of the value says about a position inside a collection.
        //
        // Named by the operation and not by "something was taken here". A count of a string and the
        // magnitude of a number at the same path are two quantities, and a flag brought them to one
        // name — so a guard bounding one would have been read against the clauses written about the
        // other (#1027).
        String spelled = term.subjectPath().stepsSpelledUnder(root);
        return switch (term) {
            case NumericTerm.ValueOf _ -> FieldDomains.Coordinate.value(spelled);
            case NumericTerm.TakenOf taken ->
                    FieldDomains.Coordinate.takenBy(spelled, taken.operation());
            // Named the same way, and named at a place no clause of the value is written at: the
            // steps run inside a sequence, and what a record says relates the fields it holds. So
            // a lookup finds nothing, which is the true answer — a record states no rule about
            // what its elements add up to — rather than a collision with the rules of a field.
            case NumericTerm.TakenOver over ->
                    FieldDomains.Coordinate.takenBy(spelled, over.operation());
        };
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
     * Where one term runs, as bounds rather than as something to add up.
     *
     * <p>Beside {@link #atOneTerm} and about the same three things. What it does not do is turn them
     * into numbers: a position ordered by its own values has ends that are values — a string stops
     * at {@code "A"} — and the arithmetic that adds terms together has no word for one.
     */
    private NumericDomain.Bounds whereOneTermRuns(NumericTerm term) {
        NumericDomain.Bounds runs = meeting(ownOf(term), term.intrinsicBounds());
        Fixed fixedAt = fixed.get(term);
        // Where two values were fixed there, between them: the rules leave nothing at all, which
        // {@link #emptiness} says, and a range that crossed itself is not something to hand a
        // caller that has not asked.
        return fixedAt == null ? runs
                : meeting(runs, new NumericDomain.Bounds(Endpoint.inclusive(fixedAt.least()),
                        Endpoint.inclusive(fixedAt.most())));
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
        Position at = byPath.get(term.subjectPath());
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
    private static RationalCut asCut(Endpoint end) {
        return end == null || !(end.at() instanceof Count at) ? null
                : new RationalCut(Rational.of(at.at()), end.inclusive());
    }

}
