package souther.compiler.partition;

import souther.compiler.ast.Ast;
import souther.compiler.check.Carrier;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.InvariantBound;
import souther.compiler.check.NumericMeasures;
import souther.compiler.codegen.InvariantConstraints;
import souther.compiler.diag.SourceRef;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * The equivalence classes a model already states, read off the types a behavior takes.
 *
 * <p>A type's cases are the classes; a threshold in an invariant is where one class ends and the next
 * begins. Nothing is invented: a position the model draws no line through has no classes, and is
 * reported as not derivable. An {@code Int} with no invariant is not silently split at zero, because
 * that would measure coverage of a rule the model never stated and report a gap for failing to test it.
 */
public final class Partitions {

    /** How deep a product is taken apart. Two levels reach a field of a record a parameter holds,
     * which is where domain rules are written; below that a report stops being about anything the
     * author would recognise as one input. */
    static final int MAX_DEPTH = 2;

    /** How many axes one behavior is measured at. Past this the pairs are more than a person reads. */
    static final int MAX_AXES = 12;

    /**
     * A position dropped for being past the limit, and what dropping it cost.
     *
     * <p>The two are not the same loss. An axis with a cut in it was carrying boundaries some rule
     * drew, and nothing can ask about them now — what the rows cover there is unknown rather than
     * complete. An axis with only classes was carrying a measure nothing refuses a build over, so
     * losing it costs a line in a report and no more. Recorded here because the difference cannot be
     * read back afterwards: neither leaves a boundary behind, and a position nobody measured looks
     * exactly like one the rows cover.
     *
     * @param axis                which position was dropped
     * @param carriedAnObligation whether a rule had drawn a line on this position
     */
    public record OmittedAxis(AxisId axis, boolean carriedAnObligation) {}

    /**
     * @param axes    the positions this behavior is measured at, in parameter order
     * @param omitted axes past {@link #MAX_AXES}, dropped rather than merged: an axis whose path
     *                nobody can name is not an axis, and folding several into one would put a class
     *                nothing can classify into the denominator
     */
    public record Partitioning(List<Axis> axes, List<OmittedAxis> omitted,
                               Map<NumericTerm, NumericDomain.Bounds> domains,
                               java.util.Set<NumericTerm> uncertain,
                               List<UndividedPosition> undivided,
                               List<UnreadRule> unread) {
        public Partitioning {
            axes = List.copyOf(axes);
            omitted = List.copyOf(omitted);
            domains = Map.copyOf(domains);
            uncertain = java.util.Set.copyOf(uncertain);
            undivided = List.copyOf(undivided);
            unread = List.copyOf(unread);
        }

        /** Whether an edge of this term is a value some row could carry.
         *
         * <p>False where a rule reaching the value the term is taken of was not read in full. Every
         * edge here is then where the rules this could read stop, and a rule it could not read can
         * refuse that value as easily as the one beyond it — so the edge is not known to be writable
         * and asking for a row at it is asking for work nobody may be able to do. */
        public boolean edgeIsKnownWritable(NumericTerm term) {
            return !uncertain.contains(term);
        }

        /** Only the positions the model actually divides. */
        public List<Axis> derivable() {
            return axes.stream().filter(Axis::derivable).toList();
        }
    }

    /** The axes of one behavior. {@code sig} says the types; {@code behavior} says the parameter names,
     * which is what a path is written from. */
    public static Partitioning of(Ast.SpecBehavior behavior, Sig sig, Symbols symbols,
                                  Exclusions excluded) {
        List<Axis> found = new ArrayList<>();
        Map<NumericTerm, NumericDomain.Bounds> domains = new LinkedHashMap<>();
        java.util.Set<NumericTerm> uncertain = new java.util.LinkedHashSet<>();
        java.util.Set<String> stopped = new java.util.LinkedHashSet<>();
        List<UnreadRule> unread = new ArrayList<>();
        for (int i = 0; i < sig.inputTypes().size() && i < behavior.params().size(); i++) {
            // One reading per parameter, not one per record met on the way down. A clause on the
            // outer record relates positions at any depth it can name, and rebuilding the reading at
            // each record is how `interval.startsAt < cap` stopped reaching `interval.startsAt`.
            Type type = sig.inputTypes().get(i);
            walk(behavior.name(), TermPath.of(behavior.params().get(i).name()), type,
                    0, symbols, found, new Placed(nameOf(type), fieldDomainsOf(type, symbols)),
                    domains, uncertain, stopped, unread);
        }
        found.replaceAll(axis -> axis.excluding(
                excluded.at(axis.path()).stream().map(TypeName::name).toList()));
        List<Axis> kept = new ArrayList<>();
        List<OmittedAxis> omitted = new ArrayList<>();
        int measured = 0;
        for (Axis axis : found) {
            if (!axis.measurable()) {
                kept.add(axis);   // kept so a report can name what it could not measure
            } else if (measured < MAX_AXES) {
                kept.add(axis);
                measured++;
            } else {
                // Whether this one was carrying an obligation is decided here and not later. A cut is
                // where a boundary comes from, and an axis dropped before `withThresholds` never gets
                // the ones a `guard` would have drawn — so what it has now is what it had. A position
                // that could take a threshold and has no cut yet is not measurable at all and is kept;
                // one with classes and no cuts is a sum or a `Bool`, which no comparison divides.
                omitted.add(new OmittedAxis(axis.id(), !axis.cuts().isEmpty()));
            }
        }
        // A position undivided because a rule about it went unread says that here, without waiting
        // for a body: a type bounded by a rule this cannot read is one whether or not any behavior
        // compares it.
        List<UndividedPosition> undivided = new ArrayList<>();
        for (UndividedPosition each : undividedIn(kept, stopped)) {
            UndividedPosition.Reason why = unread.stream()
                    .filter(one -> one.at().equals(each.at())).map(UnreadRule::why)
                    .findFirst().orElse(null);
            undivided.add(why == null ? each : each.because(why));
        }
        return new Partitioning(kept, omitted, domains, uncertain, undivided,
                List.copyOf(unread));
    }

    /**
     * The positions with no classes, each saying which of the two it is.
     *
     * <p>Derived from the axes rather than recorded beside them, so that a position measured after a
     * threshold arrives leaves this list by the same rule it entered it. {@code stopped} names the
     * ones the walk did not finish, which is the one thing the axes cannot say for themselves: an
     * axis that was never descended into looks exactly like one there was nothing under.
     */
    private static List<UndividedPosition> undividedIn(List<Axis> axes,
                                                       java.util.Set<String> stopped) {
        List<UndividedPosition> out = new ArrayList<>();
        for (Axis axis : axes) {
            if (axis.measurable()) {
                continue;
            }
            out.add(stopped.contains(axis.path().toString())
                    ? UndividedPosition.cannotDerive(axis.path(),
                            UndividedPosition.Reason.DEPTH_LIMIT)
                    : UndividedPosition.absent(axis.path()));
        }
        return List.copyOf(out);
    }

    /**
     * The same axes, with what the behavior's own comparisons divide them into.
     *
     * <p>This is where a numeric position stops being one undivided range. A type's invariant bounds
     * what can exist; a {@code guard} says where the behavior does something else, and both sides of
     * that line hold values a row can write. The cuts merge into one partition and the origins stay
     * apart, so reaching the line through one rule still leaves the others unmet.
     */
    public static Partitioning withThresholds(Partitioning base, List<Threshold> thresholds,
                                              Symbols symbols) {
        return withThresholds(base, thresholds, symbols, List.of());
    }

    /**
     * The same, told which positions a comparison names that nothing turned into a line.
     *
     * <p>A position left undivided is not thereby a position the model divides no way. What this
     * takes in is the other half of that: the body compared it, and the form the comparison is
     * written in is one no reader here takes apart. Carried rather than re-derived, because the only
     * place that knows is the reader that gave up.
     */
    public static Partitioning withThresholds(Partitioning base, List<Threshold> thresholds,
                                              Symbols symbols,
                                              List<UnreadRule> unread) {
        return withThresholds(base, thresholds, symbols, unread, List.of());
    }

    /**
     * The same, with the values a body singles out as well.
     *
     * <p>An equality is not a place to cut. What it distinguishes is one value from every other,
     * so where nothing else divides the position its classes are those two — and the second of them
     * is not a range, which is a thing a class is allowed not to be. Where an ordering comparison
     * divides the position as well, the model has drawn the further distinction itself and the value
     * is one more line among the ranges.
     */
    public static Partitioning withThresholds(Partitioning base, List<Threshold> thresholds,
                                              Symbols symbols,
                                              List<UnreadRule> unread,
                                              List<GuardThresholds.Guards.Singled> singled) {
        List<Axis> out = new ArrayList<>();
        for (Axis axis : base.axes()) {
            NumericTerm declared = axis.term();
            NumericTerm term = declared;
            List<Threshold> here = thresholds.stream()
                    .filter(t -> t.term().equals(declared)).toList();
            List<GuardThresholds.Guards.Singled> points = singled.stream()
                    .filter(one -> one.term().equals(declared)).toList();
            if (here.isEmpty() && !points.isEmpty()) {
                // Nothing orders this position, so its classes are the values singled out and
                // everything else. Ranges here would ask the rows for a distinction between the two
                // sides of a value the behavior treats alike.
                NumericDomain.Bounds only = domainOf(base, term);
                out.add(new Axis(axis.id(), term, axis.type(),
                        singledClasses(points, term, axis.type(), only, symbols),
                        mergedPoints(axis.cuts(), points, term.carrierAt(axis.type(), symbols)))
                        .excluding(axis.excluded()));
                continue;
            }
            if (here.isEmpty()) {
                // A position no rule divides, whose body measures some other number of it: a bare
                // `List<String>` nothing bounds, under a `guard List.length(t.names) > 0`. The line
                // is on that number, so the axis becomes one about it — there was nothing else here
                // for it to be about, and dropping the threshold would lose a line the body draws.
                NumericTerm drawn = axis.measurable() ? null : soleTermAt(thresholds, axis.path());
                if (drawn == null) {
                    out.add(axis);
                    continue;
                }
                term = drawn;
                here = thresholds.stream().filter(t -> t.term().equals(drawn)).toList();
                axis = new Axis(new AxisId(axis.id().behavior(), drawn.toString()), drawn,
                        axis.type(), axis.classes(), axis.cuts(), axis.excluded());
            }
            // What this term's values can be, which is the type's bound already narrowed by whatever
            // the record it sits in says about it. Reading the type again here would put a threshold
            // back inside a range the record has no values in.
            NumericDomain.Bounds domain = domainOf(base, term);
            // Filtered once, and both answers read the filtered list. A line outside what the
            // position holds divides nothing, and it is not a boundary either: leaving it in the
            // cuts while the intervals dropped it asks for a row at a value the record refuses,
            // which is the thing being fixed here happening again one field over. The end the
            // position stops short of is outside it as much as anything past it is.
            List<Threshold> reachable = here.stream()
                    .filter(t -> domain == null || domain.admits(t.value()))
                    .toList();
            // What the term is, not what an invariant said about it. There is a bound to read only
            // where the type is a newtype carrying one, and a plain `Decimal` has none — read off the
            // bound, every such position would be called an integer and a threshold of `0.5m` would
            // be asked for its exact `long`. A size is a whole number whatever it is a size of.
            Carrier carrier = term.carrierAt(axis.type(), symbols);
            // The ranges a cut leaves, where the position has no finer partition of its own. On an
            // enumeration it has: the cases are the classes, and `s < Qualified` divides them into
            // `{Prospecting}` and `{Qualified, Won}`, which is coarser than the cases. The meet of
            // the two is the case partition, so the cut adds no class — and a class list rebuilt
            // from the ranges would take away distinctions the model already made. The line is still
            // a line and still owes its rows; only the classes stay as they were.
            List<PartitionClass> classes = carrier instanceof Carrier.Ordinal ? List.of()
                    : Intervals.classesOf(
                            Intervals.of(reachable, domain == null ? null : domain.min(),
                                    domain == null ? null : domain.max()),
                            term, axis.type(), symbols);
            // Through `excluding`, so that a class list replaced by the intervals a threshold cuts
            // keeps only the exclusions it still has classes for.
            out.add(new Axis(axis.id(), term, axis.type(),
                    classes.isEmpty() ? axis.classes() : classes,
                    merged(axis.cuts(), reachable, carrier)).excluding(axis.excluded()));
        }
        // Both producers of one kind of evidence. What a body compared and what a type's own rules
        // bound are read by different readers and answer the same question, so a position either of
        // them wrote about and neither could turn into a line is named once, whichever wrote it.
        List<UnreadRule> rules = new ArrayList<>(base.unread());
        for (UnreadRule each : unread) {
            if (rules.stream().noneMatch(had -> had.equals(each))) {
                rules.add(each);
            }
        }
        List<UndividedPosition> undivided = new ArrayList<>();
        for (UndividedPosition each : undividedIn(out, java.util.Set.of())) {
            UndividedPosition had = base.undivided().stream()
                    .filter(before -> before.at().equals(each.at())).findFirst().orElse(each);
            UndividedPosition.Reason stopped = rules.stream()
                    .filter(one -> one.at().equals(each.at())).map(UnreadRule::why)
                    .findFirst().orElse(null);
            undivided.add(stopped == null ? had : had.because(stopped));
        }
        return new Partitioning(out, base.omitted(), domainsOf(base, out), base.uncertain(),
                undivided, List.copyOf(rules));
    }

    /**
     * The classes a position divided only by equalities has: each value singled out, and the rest.
     *
     * <p>The last of those is not an interval and is not asked to be. What a class needs is a way to
     * say whether a value is in it and a value that stands for it, and a complement has both — the
     * shape a class has been limited to is what this is here to stop being the limit.
     */
    private static List<PartitionClass> singledClasses(List<GuardThresholds.Guards.Singled> points,
                                                       NumericTerm term, Type type,
                                                       NumericDomain.Bounds within, Symbols symbols) {
        Carrier carrier = term.carrierAt(type, symbols);
        TypeName wrapper = type instanceof Type.Ref ref && TypeOps.isSingleValueNewtype(type, symbols)
                ? ref.name() : null;
        List<Count> values = new ArrayList<>();
        for (GuardThresholds.Guards.Singled each : points) {
            if (values.stream().noneMatch(had -> had.sameAs(each.value()))) {
                values.add(each.value());
            }
        }
        List<PartitionClass> classes = new ArrayList<>();
        for (Count value : values) {
            String written = carrier.written(value);
            classes.add(PartitionClass.of(term + "/= " + written, "= " + written,
                    holding(term, carrier, at -> at.sameAs(value)),
                    RepresentativeSource.of(FixtureTemplate.on(carrier, value, wrapper))));
        }
        Count other = otherThan(values, within, carrier);
        String label = "/= " + String.join(", ",
                values.stream().map(carrier::written).toList());
        classes.add(other == null
                ? PartitionClass.ungeneratable(term + "/" + label, label,
                        holding(term, carrier, at -> values.stream().noneMatch(at::sameAs)),
                        "nothing here composed a value of this position other than the ones"
                                + " singled out")
                : PartitionClass.of(term + "/" + label, label,
                        holding(term, carrier, at -> values.stream().noneMatch(at::sameAs)),
                        RepresentativeSource.of(FixtureTemplate.on(carrier, other, wrapper))));
        return List.copyOf(classes);
    }

    /** A classifier that reads the term's count out of a row and answers about it. */
    private static Classifier holding(NumericTerm term, Carrier carrier,
                                      java.util.function.Predicate<Count> holds) {
        return value -> switch (term.read(value, carrier)) {
            case NumericTerm.Reading.Number number -> Membership.of(holds.test(number.value()));
            case NumericTerm.Reading.Missing missing -> new Membership.Incomplete(missing.code());
            case NumericTerm.Reading.NotNumber _ -> Membership.NO_MATCH;
        };
    }

    /**
     * A number the position holds that is none of {@code values}, or null where this found none.
     *
     * <p>Where the values step, the one beside a singled-out value is the nearest thing to it and is
     * tried first. Over a dense carrier there is no step to take: a value bounded to `+[0, 1]+` and
     * singled out at `+0.5+` steps to `+1.5+` and `+-0.5+`, both outside, and neither says anything
     * about whether the class has values — it holds `+0+`, `+1+` and everything between. So the ends
     * of what the position admits are asked, and a value between them, before any step is.
     *
     * <p>Null is this having found none and never the class being empty. Nothing here enumerates a
     * dense range, so what a caller may say about an empty answer is that it composed nothing.
     */
    private static Count otherThan(List<Count> values, NumericDomain.Bounds within, Carrier carrier) {
        List<Count> stepped = new ArrayList<>();
        for (Count from : values) {
            stepped.add(from.plus(1));
            stepped.add(from.minus(1));
        }
        List<Count> inside = new ArrayList<>();
        if (within != null) {
            for (Endpoint end : List.of(within.min(), within.max())) {
                if (end != null && end.inclusive()) {
                    inside.add(end.at());
                }
            }
            Count between = Endpoint.valueBetween(within.min(), within.max(), carrier.spacing());
            if (between != null) {
                inside.add(between);
            }
            // Between the count singled out and each end, which is where a dense range still has
            // room once the ends themselves are singled out too.
            for (Count from : values) {
                for (Endpoint end : List.of(within.min(), within.max())) {
                    if (end != null) {
                        inside.add(Endpoint.valueBetween(Endpoint.exclusive(from), end,
                                carrier.spacing()));
                        inside.add(Endpoint.valueBetween(end, Endpoint.exclusive(from),
                                carrier.spacing()));
                    }
                }
            }
        }
        List<Count> tried = new ArrayList<>();
        if (carrier == Carrier.DENSE) {
            tried.addAll(inside);
            tried.addAll(stepped);
        } else {
            tried.addAll(stepped);
            tried.addAll(inside);
        }
        for (Count candidate : tried) {
            // On the carrier's grid before it is asked anything. Halfway between two adjacent moments
            // is neither of them as a number and is one of them once written, so a class of
            // everything else was offered one of the values it exists to exclude.
            Count each = carrier.onTheGrid(candidate);
            if (each != null && (within == null || within.admits(each))
                    && values.stream().noneMatch(each::sameAs)) {
                return each;
            }
        }
        return null;
    }

    /** The cuts a position has, with the values a body singled out added as lines of their own. */
    private static List<Cut> mergedPoints(List<Cut> had, List<GuardThresholds.Guards.Singled> points,
                                          Carrier carrier) {
        Map<String, Cut> byValue = new LinkedHashMap<>();
        for (Cut cut : had) {
            byValue.put(cut.key(), cut);
        }
        for (GuardThresholds.Guards.Singled each : points) {
            Cut cut = Cut.at(carrier, each.value(), each.origin());
            byValue.merge(cut.key(), cut, (there, _) -> there.and(each.origin()));
        }
        return List.copyOf(byValue.values());
    }

    /**
     * The one term a body draws lines on at {@code path}, or null where it draws none or draws them
     * on more than one.
     *
     * <p>More than one is left alone rather than picked between. A position carrying two axes is a
     * shape this can hold and nothing yet produces, and choosing one of them here would silently
     * drop the other's lines.
     */
    private static NumericTerm soleTermAt(List<Threshold> thresholds, TermPath path) {
        NumericTerm found = null;
        for (Threshold each : thresholds) {
            if (!each.term().path().equals(path)) {
                continue;
            }
            if (found != null && !found.equals(each.term())) {
                return null;
            }
            found = each.term();
        }
        return found;
    }

    private static NumericDomain.Bounds domainOf(Partitioning base, NumericTerm term) {
        NumericDomain.Bounds read = base.domains().get(term);
        return read != null ? read : term.ownBounds();
    }

    /** The domains, with an entry for a term an axis only took on here. What a term guarantees about
     * its own values is what bounds it where no rule was written about it. */
    private static Map<NumericTerm, NumericDomain.Bounds> domainsOf(Partitioning base,
                                                                    List<Axis> axes) {
        Map<NumericTerm, NumericDomain.Bounds> out = new LinkedHashMap<>(base.domains());
        for (Axis axis : axes) {
            NumericDomain.Bounds own = axis.term().ownBounds();
            if (own != null) {
                out.putIfAbsent(axis.term(), own);
            }
        }
        return out;
    }

    /** The cuts a position has, with a rule that drew one already there recorded rather than repeated:
     * an invariant and a guard that state the same bound are one cut and two obligations. */
    private static List<Cut> merged(List<Cut> had, List<Threshold> thresholds, Carrier carrier) {
        Map<String, Cut> byValue = new LinkedHashMap<>();
        for (Cut cut : had) {
            byValue.put(cut.key(), cut);
        }
        for (Threshold each : thresholds) {
            Cut cut = Cut.at(carrier, each.value(), each.origin());
            byValue.merge(cut.key(), cut, (there, _) -> there.and(each.origin()));
        }
        return List.copyOf(byValue.values());
    }

    /**
     * The values a row has to be written at, one per rule that drew a cut.
     *
     * <p>An invariant's bound is met by writing the value: outside it nothing can be constructed, so
     * the edge is the only row there is to write. A guard's line has values on both sides, so it wants
     * the value and its neighbour — and the neighbour only where the type has one to give.
     */
    public static List<BoundaryObligation> obligationsOf(Axis axis, Symbols symbols,
                                                         NumericDomain.Bounds within) {
        BoundaryDomain domain = axis.term().intervals(axis.type(), symbols);
        List<BoundaryObligation> out = new ArrayList<>();
        for (Cut cut : axis.cuts()) {
            // A line the position does not reach. The rule that drew it did so about the type, and
            // what is left of the type here may stop short of it or leave the value out — `low < high`
            // under one `[0, 1]` leaves `low` every value up to 1 and not 1 itself. Writing the value
            // is how an edge is met, so where the value is refused there is nothing to write.
            //
            // Asked of the count, so every carrier is asked the same question. Asked of the value, a
            // date came back as a value the range could say nothing about — which read as reachable,
            // and put a row at an edge the record refuses.
            boolean reachable = within == null || within.admits(cut.at());
            for (OriginRef origin : cut.origins()) {
                if (reachable) {
                    out.add(new BoundaryObligation(axis.id(), origin,
                            BoundaryObligation.BoundarySide.AT, cut.carrier(), cut.at()));
                }
                // A line that singles a value out has no neighbour to ask for: the values either
                // side of it are one class, so a row over there is a row the class's own already is.
                if (origin instanceof OriginRef.GuardOrigin guard && !guard.singles()) {
                    // The other class's edge is the neighbour on the side the cut value is not on —
                    // where that class has values. A guard at the end of what the position can hold
                    // has nothing on one side of it, and a step off the end is a row nobody can write:
                    // `value >= 10` under `x < 10` would be owed a 9. The cut itself stays either way,
                    // because the comparison is still reached by a row written at the line.
                    if (guard.valueBelongsBelow()) {
                        domain.successor(cut.at())
                                .filter(next -> within == null || within.admits(next))
                                .ifPresent(next -> out.add(new BoundaryObligation(
                                        axis.id(), origin, BoundaryObligation.BoundarySide.ABOVE,
                                        cut.carrier(), next)));
                    } else {
                        domain.predecessor(cut.at())
                                .filter(before -> within == null || within.admits(before))
                                .ifPresent(before -> out.add(new BoundaryObligation(
                                        axis.id(), origin, BoundaryObligation.BoundarySide.BELOW,
                                        cut.carrier(), before)));
                    }
                }
            }
        }
        return List.copyOf(out);
    }

    /** One position: measured where the model divides it or bounds it, taken apart where it is a
     * record, and recorded as not derivable where it is neither. */
    private static void walk(String behavior, TermPath path, Type type, int depth, Symbols symbols,
                             List<Axis> out, Placed placed,
                             Map<NumericTerm, NumericDomain.Bounds> domains,
                             java.util.Set<NumericTerm> uncertain,
                             java.util.Set<String> stopped, List<UnreadRule> unread) {
        List<PartitionClass> classes = classesOf(type, symbols);
        // Which number this position is measured at, and what its rules leave that number. Asked
        // together because they are one reading: whether a rule bounds the length of a string is how
        // it is known that the length is the number being measured.
        Measured measured = measure(path, type, symbols);
        for (UnreadRule each : measured.unread()) {
            if (unread.stream().noneMatch(had -> had.equals(each))) {
                unread.add(each);
            }
        }
        NumericTerm term = measured.term();
        AxisId id = AxisId.of(behavior, term);
        Bounds own = measured.bounds();
        // A value whose rules contradict has no positions to cover: every edge of every field of it
        // is a row nobody can write, which is not the same answer as a field nothing bounds.
        boolean nothingExists = placed != null && placed.domains().infeasible();
        // A record's rule relates the numbers its fields hold, so it reaches the term that is one of
        // them and no other: a cap on a field says nothing about how long the string beside it is.
        NumericDomain.Bounds projected = placed == null || !(term instanceof NumericTerm.ValueOf)
                ? null : placed.at(path);
        // Two questions of one pair of readings, and they do not have one answer. What the term's
        // values can be is every rule about it intersected; where it is divided is only where its own
        // type draws a line, because a clause relating two fields is not a partition of one of them.
        NumericDomain.Bounds admissible = nothingExists ? null
                : admissibleBounds(own, projected, term);
        if (admissible != null && !admissible.isEmpty()) {
            domains.put(term, admissible);
        }
        Bounds axis = nothingExists ? null : axisBounds(own, projected);
        List<Cut> cuts = nothingExists ? List.of()
                : cutsOf(type, axis, own, placed == null ? null : placed.value());
        // Whether a row can be written at an edge is a question about the whole value the position
        // sits in, so it is answered once for the parameter. A rule this could not read is a way that
        // value can be refused, wherever in it the rule is written.
        if (!cuts.isEmpty() && placed != null && !placed.domains().allRulesRead()) {
            uncertain.add(term);
        }
        if (!classes.isEmpty() || !cuts.isEmpty()) {
            out.add(new Axis(id, term, type, classes, cuts));
            return;
        }
        Map<String, Type> fields = productFields(type, symbols);
        if (!fields.isEmpty() && depth >= MAX_DEPTH) {
            // A record this never went into. What is under it may divide, and nothing here looked.
            stopped.add(path.toString());
        }
        if (!fields.isEmpty() && depth < MAX_DEPTH) {
            for (Map.Entry<String, Type> field : fields.entrySet()) {
                walk(behavior, path.then(field.getKey()), field.getValue(), depth + 1, symbols, out,
                        placed, domains, uncertain, stopped, unread);
            }
            return;
        }
        out.add(Axis.notDerivable(id, term, type));
    }

    /** A position's number, what its own rules leave it, and which of those rules said nothing this
     * could read. */
    private record Measured(NumericTerm term, Bounds bounds, List<UnreadRule> unread) {

        Measured(NumericTerm term, Bounds bounds) {
            this(term, bounds, List.of());
        }
    }

    /**
     * The rules on this position's own type that say where its value stops and that nothing here
     * turned into an end.
     *
     * <p>The invariant's half of what a {@code guard}'s comparison is asked in {@link
     * GuardThresholds#comparedIn}. Both draw lines (ADR-0090) and both can be written in a form this
     * does not read, and only one of them was saying so — a bound it dropped left the position
     * looking like one no rule bounds, which is what the declaration above it denies.
     *
     * @param carried what the value is read on, or null where nothing here draws a line on it
     * @param measure the operation a number is taken by, or null where none is
     */
    private static List<UnreadRule> unreadBoundsAt(TermPath path, Type type, Symbols symbols,
                                                   Carrier carried, ValueName measure) {
        List<UnreadRule> out = new ArrayList<>();
        for (TypeOps.Layer layer : TypeOps.newtypeChain(type, symbols)) {
            for (Ast.InvariantClause clause : TypeOps.effectiveInvariants(layer.data(), symbols)) {
                for (Ast.Expr each : InvariantConstraints.clauses(clause.expr())) {
                    UndividedPosition.Reason why = whyUnread(each, carried, measure);
                    // Once per position, as a comparison is: what a reader has to lift is the first
                    // limit in the way, and a second clause behind it says nothing further.
                    if (why != null && out.isEmpty()) {
                        out.add(new UnreadRule(path, why));
                    }
                }
            }
        }
        return List.copyOf(out);
    }

    /** What stopped one clause from being an end, or null where nothing did — either because it was
     * read, or because it is not a rule about where the value stops. */
    private static UndividedPosition.Reason whyUnread(Ast.Expr clause, Carrier carried,
                                                      ValueName measure) {
        if (InvariantBound.statesAnEnd(clause, null)) {
            if (carried == null) {
                // The value is ordered — it is compared in the clause — and this reads no line on
                // what carries it. The carrier, asked of the carrier, as a guard's is.
                return UndividedPosition.Reason.UNSUPPORTED_DOMAIN;
            }
            return InvariantBound.of(clause, carried).isPresent()
                    ? null : UndividedPosition.Reason.UNSUPPORTED_SYNTAX;
        }
        if (measure != null && InvariantBound.statesAnEnd(clause, measure)) {
            // A size is a whole number whatever it is a size of, so nothing here is about a carrier.
            return InvariantBound.ofSize(clause, measure).isPresent() ? null
                    : UndividedPosition.Reason.UNSUPPORTED_SYNTAX;
        }
        return null;
    }

    /**
     * Which number a position is measured at.
     *
     * <p>What it holds, where that is a number. Otherwise what its rules take of it — and only where
     * they take something: a string nobody wrote a rule about is a position the model draws no line
     * through, and naming its length there would put a term in the report that nobody wrote.
     */
    private static Measured measure(TermPath path, Type type, Symbols symbols) {
        Carrier carried = Carrier.ofValue(type, symbols);
        ValueName.Stdlib of = NumericMeasures.takenOf(type, symbols);
        List<UnreadRule> unread = unreadBoundsAt(path, type, symbols, carried, of);
        if (carried != null) {
            return new Measured(new NumericTerm.ValueOf(path),
                    boundsOf(type, symbols, carried, null), unread);
        }
        if (of != null) {
            Bounds sized = boundsOf(type, symbols, Carrier.WHOLE, of);
            if (sized != null && !sized.isEmpty()) {
                return new Measured(new NumericTerm.SizeOf(of, path), sized, unread);
            }
        }
        return new Measured(new NumericTerm.ValueOf(path), null, unread);
    }

    /** The value a position is inside: what it is called, and what its rules leave each position of
     * it able to hold. */
    private record Placed(TypeName value, FieldDomains domains) {

        /** What is left for the position at {@code path}, which is read from the value this is of. */
        NumericDomain.Bounds at(TermPath path) {
            return path.fields().isEmpty() ? null
                    : domains.at(String.join(".", path.fields()));
        }
    }

    private static TypeName nameOf(Type type) {
        return type instanceof Type.Ref ref ? ref.name() : null;
    }

    /** What the record a field sits in leaves each of its fields able to hold. */
    private static FieldDomains fieldDomainsOf(Type type, Symbols symbols) {
        return type instanceof Type.Ref ref && symbols.get(ref.name()) instanceof Ast.Data data
                ? FieldDomains.of(ref.name(), data, symbols) : FieldDomains.NONE;
    }

    /**
     * Where the position is divided: the type's own bound, taken in to where the record it sits in
     * stops.
     *
     * <p>Only taken in. A record's rule moves an edge the type already has; it does not put one on a
     * position the type left open. An {@code Int} nobody bounded stays a position the model draws no
     * line through, which is what a report says of it (ADR-0090) — giving it an edge here would make
     * a rule relating two fields into a partition of one of them.
     *
     * <p>So this is not what the position can hold, and reading it as that is how a cap written on
     * the record alone became invisible: see {@link #admissibleBounds}.
     */
    private static Bounds axisBounds(Bounds own, NumericDomain.Bounds projected) {
        if (own == null || projected == null) {
            return own;
        }
        // The value moves and the names do not: a record narrowing an edge does not take it away
        // from the rule that put one there, and which record did the narrowing is said beside it.
        return new Bounds(
                own.min() == null ? null
                        : new End(Endpoint.lower(own.min().at(), projected.min()), own.min().from()),
                own.max() == null ? null
                        : new End(Endpoint.upper(own.max().at(), projected.max()), own.max().from()),
                own.carrier());
    }

    /**
     * What the position can hold: every rule reaching it, intersected.
     *
     * <p>An end survives from whichever side has one, because a value outside it is refused whether
     * the type said so or the record did. That is the difference from {@link #axisBounds}: a cap the
     * record alone imposes is not a line dividing this position, and it is still where its values
     * stop — so a guard beyond it divides nothing and is no edge either.
     *
     * <p>Numbers and no names. An end here says where the values stop; which rule put it there is a
     * cut's question, and answering it from a projection would name a rule that never mentioned this
     * position on its own.
     */
    private static NumericDomain.Bounds admissibleBounds(Bounds own, NumericDomain.Bounds projected) {
        return admissibleBounds(own, projected, null);
    }

    /**
     * The same, with what the term itself guarantees taken in.
     *
     * <p>A size is never negative and nothing has to write that down (spec
     * §invariant-discharge-terms). Kept here with the rules rather than at the boundary that reads
     * them, so that a guard at zero is refused its neighbour below by the same intersection that
     * refuses one outside an invariant.
     */
    private static NumericDomain.Bounds admissibleBounds(Bounds own, NumericDomain.Bounds projected,
                                                         NumericTerm term) {
        NumericDomain.Bounds intrinsic = term == null ? null : term.ownBounds();
        if (own == null) {
            return intrinsic;   // not a number of its own, so only what the term guarantees
        }
        Endpoint min = own.min() == null ? null : own.min().at();
        Endpoint max = own.max() == null ? null : own.max().at();
        NumericDomain.Bounds read = projected == null ? new NumericDomain.Bounds(min, max)
                : new NumericDomain.Bounds(Endpoint.lower(min, projected.min()),
                        Endpoint.upper(max, projected.max()));
        return intrinsic == null ? read
                : new NumericDomain.Bounds(Endpoint.lower(read.min(), intrinsic.min()),
                        Endpoint.upper(read.max(), intrinsic.max()));
    }

    /** A record's fields, or nothing where the type is not one. A newtype is not taken apart: its
     * {@code value} is the same position it is. */
    private static Map<String, Type> productFields(Type type, Symbols symbols) {
        if (type instanceof Type.Ref ref && symbols.get(ref.name()) instanceof Ast.Data data
                && !data.newtype()) {
            return TypeOps.fieldTypes(data, symbols);
        }
        return Map.of();
    }

    // --- what a type divides its values into ------------------------------------------------------

    static List<PartitionClass> classesOf(Type type, Symbols symbols) {
        if (type == Type.BOOL) {
            return List.of(
                    PartitionClass.of("true", "true", Classifier.byShape(v -> isBool(v, true)),
                            RepresentativeSource.of(FixtureTemplate.bool(true))),
                    PartitionClass.of("false", "false", Classifier.byShape(v -> isBool(v, false)),
                            RepresentativeSource.of(FixtureTemplate.bool(false))));
        }
        if (type instanceof Type.OptionOf option) {
            List<FixtureTemplate> some = representativesOf(option.element(), symbols);
            return List.of(
                    PartitionClass.of("None", "None",
                            Classifier.byShape(v -> v instanceof ObservedValue.Absent),
                            RepresentativeSource.of(FixtureTemplate.none())),
                    some.isEmpty()
                            ? PartitionClass.ungeneratable("Some", "Some",
                                    Classifier.byShape(v -> !(v instanceof ObservedValue.Absent)),
                                    "nothing here composed a value of "
                                            + Type.show(option.element()))
                            : PartitionClass.of("Some", "Some",
                                    Classifier.byShape(v -> !(v instanceof ObservedValue.Absent)),
                                    () -> some));
        }
        if (TypeOps.isSumType(type, symbols)) {
            List<PartitionClass> cases = new ArrayList<>();
            for (TypeName leaf : TypeOps.leafCases(type, symbols)) {
                cases.add(caseClass(leaf, symbols));
            }
            return cases;
        }
        // A numeric newtype's invariant does not divide the values a row can write. Everything outside
        // it is refused at construction (E1903), so there is no class on the other side to cover — the
        // bound leaves a boundary to reach, not a partition to fill. What does divide the values a row
        // can write is a threshold a behavior compares against, which is read from the body.
        return List.of();
    }

    private static PartitionClass caseClass(TypeName leaf, Symbols symbols) {
        Classifier is = Classifier.byShape(v -> switch (v) {
            case ObservedValue.Unit u -> leaf.equals(u.type());
            case ObservedValue.Constructed c -> leaf.equals(c.type());
            default -> false;
        });
        if (!(symbols.get(leaf) instanceof Ast.Data data)) {
            return PartitionClass.of(leaf.name(), leaf.name(), is,
                    RepresentativeSource.of(FixtureTemplate.unitCase(leaf)));   // naming it builds it
        }
        if (data.newtype()) {
            List<FixtureTemplate> inner = insideTheNewtype(leaf, symbols);
            return inner.isEmpty()
                    ? PartitionClass.ungeneratable(leaf.name(), leaf.name(), is,
                            "nothing here composed a value of what `" + leaf.name() + "` wraps")
                    : PartitionClass.of(leaf.name(), leaf.name(), is,
                            () -> inner.stream().map(t -> FixtureTemplate.newtype(leaf, t)).toList());
        }
        // A record case is written field by field, which is the generator's composition. So the class
        // names the constructor and the generator does the composing — the same walk every other
        // record goes through, rules between the fields and all.
        return PartitionClass.composed(leaf.name(), leaf.name(), is, leaf);
    }

    // --- reading an invariant's bounds -------------------------------------------------------------

    /** What a newtype's invariant says about the range of its value. */
    /**
     * One end of a range, and every name that put it there.
     *
     * <p>Names, plural. Two layers can state the same bound — a wrapper repeating what it wraps — and
     * they are two rules a row could be owed to, which is the accounting a cut already keeps. Holding
     * one would drop an obligation rather than a line of text.
     */
    private record End(Endpoint at, List<TypeName> from) {

        Count value() {
            return at.at();
        }

        /**
         * This end, or {@code other} where it is the stronger, or both where they agree.
         *
         * <p>Which number survives and whether the value is one of the range's own are the same
         * question asked of {@link Endpoint}, so that this and the domain cannot disagree about it.
         * Where the two are at one number both names are kept: each is a rule the line is owed to,
         * however far into the range each of them reaches.
         */
        static End tighter(End had, End one, boolean upper) {
            if (one == null) {
                return had;
            }
            if (had == null) {
                return one;
            }
            Endpoint at = upper ? Endpoint.upper(had.at(), one.at()) : Endpoint.lower(had.at(), one.at());
            if (had.value().compareTo(one.value()) != 0) {
                return at == had.at() ? had : one;
            }
            List<TypeName> both = new ArrayList<>(had.from());
            one.from().stream().filter(n -> !both.contains(n)).forEach(both::add);
            return new End(at, List.copyOf(both));
        }
    }

    /**
     * What a newtype's rules leave the value between, and which of the names it wears said so.
     *
     * <p>The layer is kept because a boundary is reported by the rule that drew it, and a value
     * wearing two names is bounded by rules written on either. Read off the outermost name, an edge
     * that `Minute` drew would be reported as `StartMinute`'s.
     */
    private record Bounds(End min, End max, Carrier carrier) {

        boolean isEmpty() {
            return min == null && max == null;
        }

        /** Whether the values here have no smallest step, which is what decides where a strict bound
         *  leaves an end. */
        boolean decimal() {
            return carrier == Carrier.DENSE;
        }
    }

    /** What a numeric newtype's own rules leave its value between, for a caller that is asking about
     * the value and not about anything taken of it. */
    private static Bounds boundsOf(Type type, Symbols symbols) {
        return boundsOf(type, symbols, Carrier.ofValue(type, symbols), null);
    }

    /**
     * @param carrier what the clauses' values are read on, or null where nothing here reads them
     * @param measure the operation the number is taken by, or null where the number is the value
     *                itself
     */
    private static Bounds boundsOf(Type type, Symbols symbols, Carrier carrier, ValueName measure) {
        if (carrier == null) {
            return null;
        }
        End min = null;
        End max = null;
        // Every name the value wears, not the outermost one. A rule written on the type a newtype
        // wraps bounds the value as much as one written on the newtype does, and the two intersect:
        // `Inner: value >= 0` under `Outer: value <= 10` is a range of `[0, 10]`, and neither layer
        // alone says so. How far that reaches is asked of `TypeOps` rather than walked again here,
        // and every layer that put an end where it is is kept, because each is a rule a row is owed.
        for (TypeOps.Layer layer : TypeOps.newtypeChain(type, symbols)) {
            for (Ast.InvariantClause clause : TypeOps.effectiveInvariants(layer.data(), symbols)) {
                for (Ast.Expr each : InvariantConstraints.clauses(clause.expr())) {
                    InvariantBound read = (measure == null ? InvariantBound.of(each, carrier)
                            : InvariantBound.ofSize(each, measure)).orElse(null);
                    if (read == null) {
                        continue;
                    }
                    End end = new End(read.end(), List.of(layer.named()));
                    if (read.lower()) {
                        min = End.tighter(min, end, false);
                    } else {
                        max = End.tighter(max, end, true);
                    }
                }
            }
        }
        return new Bounds(min, max, carrier);
    }

    /** The cuts of a position, each carrying the rule that drew it. */
    /**
     * The cuts of a position whose range is already settled.
     *
     * @param bounds where the position stops, the record it sits in taken into account
     * @param own    where its own type stops, so that an end the record moved can say so
     * @param within the record, or null at a position that is not a field of one
     */
    private static List<Cut> cutsOf(Type type, Bounds bounds, Bounds own, TypeName within) {
        if (bounds == null || bounds.isEmpty() || !(type instanceof Type.Ref)) {
            return List.of();
        }
        Map<String, Cut> byValue = new LinkedHashMap<>();
        cut(byValue, bounds.min(), own == null ? null : own.min(), "min",
                bounds.carrier(), within);
        cut(byValue, bounds.max(), own == null ? null : own.max(), "max",
                bounds.carrier(), within);
        return List.copyOf(byValue.values());
    }

    /** One end as a cut, owed once to each rule that put it there. */
    private static void cut(Map<String, Cut> into, End end, End own, String clause, Carrier carrier,
                            TypeName within) {
        if (end == null) {
            return;
        }
        // Taken in, which a record can do by moving the end or by taking away the value it stops
        // at. `low < high` under one `[0, 1]` leaves `low` the same 1 and no longer holding it, and
        // that is the record's doing as much as a smaller number would have been.
        boolean moved = own != null && !own.at().equals(end.at());
        for (TypeName from : end.from()) {
            put(into, carrier, end.value(), from, clause, moved ? within : null);
        }
    }

    /** Whether an end is somewhere other than where the type's own rule left it. */
    private static boolean moved(BigDecimal own, BigDecimal effective) {
        return own != null && own.compareTo(effective) != 0;
    }

    private static void put(Map<String, Cut> into, Carrier carrier, Count at, TypeName type,
                            String clause, TypeName narrowedBy) {
        OriginRef origin = new OriginRef.InvariantOrigin(Optional.<SourceRef>empty(), type, clause);
        if (narrowedBy != null) {
            origin = new OriginRef.NarrowedOrigin(origin, narrowedBy);
        }
        OriginRef each = origin;
        Cut cut = Cut.at(carrier, at, origin);
        into.merge(cut.key(), cut, (had, _) -> had.and(each));
    }

    // --- small helpers ----------------------------------------------------------------------------

    /** Values that could stand for a type wherever nothing else has been said about the position — the
     * inner value of a newtype, a field no axis divides. A record is not one of these: its fields are
     * composed, which is the generator's work and not a value this can hand over. */
    static List<FixtureTemplate> representativesOf(Type type, Symbols symbols) {
        return representativesOf(type, symbols, null);
    }

    /**
     * The same, for a position the record it sits in has already narrowed.
     *
     * <p>{@code within} is what is left of the position once the rest of the assignment is settled:
     * an {@code endsAt} beside a {@code startsAt} of 1439 can only be 1440, and the value this offers
     * has to come from there rather than from the bottom of the type's own range.
     */
    static List<FixtureTemplate> representativesOf(Type type, Symbols symbols,
                                                   NumericDomain.Bounds within) {
        return representativesOf(type, symbols, within, java.util.Set.of());
    }

    /**
     * The same, with the newtypes this is already inside the value of.
     *
     * <p>Carried because what stands for a collection is built from what stands for its element, which
     * is this question again. A name met while its own value is being built is a type written in terms
     * of itself and is given up on — the names and not a count of them, since how many names a value
     * wears on the way down is not what has to be stopped.
     */
    static List<FixtureTemplate> representativesOf(Type type, Symbols symbols,
                                                   NumericDomain.Bounds within,
                                                   java.util.Set<TypeName> expanding) {
        if (type == null) {
            return List.of();
        }
        if (type == Type.INT || type == Type.DECIMAL) {
            Carrier carrier = type == Type.DECIMAL ? Carrier.DENSE : Carrier.WHOLE;
            Count at = inside(within, carrier);
            return at == null ? List.of() : List.of(FixtureTemplate.on(carrier, at, null));
        }
        if (type == Type.STRING) {
            return List.of(FixtureTemplate.string("x"));
        }
        if (type == Type.BOOL) {
            return List.of(FixtureTemplate.bool(true));
        }
        // A date is built from its ISO 8601 form, which is how a row writes one. One fixed day rather
        // than today's: a generated row is compared with the last one to see what changed, and a value
        // that read the clock would change every time nothing had.
        if (type == Type.DATE) {
            return List.of(FixtureTemplate.date("2000-01-01"));
        }
        if (type == Type.DATETIME) {
            return List.of(FixtureTemplate.dateTime("2000-01-01T00:00:00"));
        }
        // The empty one, for every collection nothing has said otherwise about. A row whose collection
        // is not what it is about should say so by carrying nothing, and where no rule counts what the
        // position holds there is nothing else to go on. What a rule does say is read a layer out, at
        // the newtype the rule is written on.
        if (type instanceof Type.ListOf || type instanceof Type.SetOf || type instanceof Type.MapOf) {
            return List.of(FixtureTemplate.emptyCollection());
        }
        List<PartitionClass> classes = classesOf(type, symbols);
        for (PartitionClass each : classes) {
            // Values, not a class that could produce one. A class whose values are composed has none
            // to hand over here, and returning its empty list would say the type has no values.
            if (each.generatable() && !each.representatives().candidates().isEmpty()) {
                return each.representatives().candidates();
            }
        }
        // A newtype the model only bounds has no classes — everything outside the bound is refused at
        // construction — but it does have values, and the edge of the bound is one that builds.
        if (type instanceof Type.Ref ref && symbols.get(ref.name()) instanceof Ast.Data data
                && data.newtype()) {
            return insideTheNewtype(ref.name(), symbols, within, expanding).stream()
                    .map(t -> FixtureTemplate.newtype(ref.name(), t)).toList();
        }
        return List.of();
    }

    /**
     * How many of whatever counts a value the rules on its type require it to hold, or 0 where they
     * require none.
     *
     * <p>Which operation counts it is asked of {@link NumericMeasures}, the one list of them, so that
     * a rule this reads and a rule a boundary is drawn on are read off the same call. Not asked of the
     * decoder's constraints: Raoh has no entry for a set's size — a set crosses the boundary as a list
     * and a size chained after the mapping that drops duplicates would count the wrong things — and
     * that absence is a fact about the decoder rather than about what the rule says.
     */
    static int leastHeld(Type type, Symbols symbols) {
        ValueName.Stdlib counts = NumericMeasures.takenOf(type, symbols);
        if (counts == null) {
            return 0;
        }
        Bounds sized = boundsOf(type, symbols, Carrier.WHOLE, counts);
        if (sized == null || sized.min() == null) {
            return 0;
        }
        // A count is a whole number, so the end a size bound leaves is one the rule admits.
        int least = Counts.asSize(sized.min().value());
        return least <= 0 ? 0 : least;
    }

    /**
     * Why a position offered less than its rules allow, or null where it offered everything.
     *
     * <p>Two things are told apart from a refusal here, and both are facts about this rather than about
     * the model. A count past what a row is built to carry means no value of the shape the rule asks
     * for was built at all — a list of a million exists and somebody could write one — so a reader told
     * "every value tried was refused" would go looking for the rule that refuses a value nothing
     * refuses. More pairings between a map's key and value than are built at once means values of the
     * shape were built and refused and more of them were never reached, which is a search that stopped.
     *
     * <p>Asked only where nothing was written. It re-reads what a position could have offered, and a
     * row that was written has no reason to pay for that.
     */
    static Generator.UnresolvedCombination.Reason notBuilt(Type type, Symbols symbols) {
        return Witnesses.heldBackFor(TypeOps.base(type, symbols), leastHeld(type, symbols), symbols);
    }

    /**
     * The {@code index}th number the rules on {@code type} leave it able to hold, or null where it has
     * no such number.
     *
     * <p>Asked where several values of one type are needed and they have to differ — the elements of a
     * set, the keys of a map. Counted from inside the range rather than from zero, because a second
     * value the type itself refuses would have the collection refused for its elements while saying
     * nothing about how many of them there are.
     *
     * <p>Only a whole number steps. Between two decimals there is no next value, so a dense carrier
     * names the one number inside its range and no more.
     */
    static Count numberInside(Type type, Symbols symbols, int index) {
        Type base = TypeOps.numericBase(type, symbols);
        if (base == null) {
            return null;
        }
        NumericDomain.Bounds range = admissibleBounds(boundsOf(type, symbols), null);
        Count from = inside(range, base == Type.DECIMAL ? Carrier.DENSE : Carrier.WHOLE);
        if (from == null || base != Type.INT) {
            return from != null && index == 0 ? from : null;
        }
        Count stepped = from.plus(index);
        return holdsCount(range, stepped) ? stepped : null;
    }

    /**
     * The same, with a second value offered at a numeric position.
     *
     * <p>One value is enough only where the rules that decide it are the rules the projection holds.
     * A disequality is a hole no range keeps, and a form that is neither an interval nor a difference
     * is not recorded at all — so the value a range gives up can be one those rules refuse, and a
     * position offering only that has nothing left to try.
     *
     * <p>Displaced and not invented. A whole number has a next one; a decimal between two ends has a
     * midpoint, and where it has no second end it gets no second value, because an epsilon is a value
     * the type does not name. A candidate is a proposal the decoder answers — it carries no promise
     * that the value is writable, which is what separates this from a boundary a person is asked to
     * write.
     */
    static List<FixtureTemplate> displacedRepresentativesOf(Type type, Symbols symbols,
                                                            NumericDomain.Bounds within) {
        List<FixtureTemplate> base = new ArrayList<>(representativesOf(type, symbols, within));
        // What a position holds back for the product search's second pass is on offer here from the
        // start. This pass runs only where both of those have already failed, and a position keeping
        // a value from the last search there is a value nothing will ever be tried at.
        for (FixtureTemplate held : inReserve(type, symbols, within)) {
            if (base.stream().noneMatch(each -> each.text().equals(held.text()))) {
                base.add(held);
            }
        }
        Type numeric = TypeOps.numericBase(type, symbols);
        if (numeric == null) {
            return List.copyOf(base);
        }
        NumericDomain.Bounds range = admissibleBounds(boundsOf(type, symbols), within);
        Carrier carrier = numeric == Type.INT ? Carrier.WHOLE : Carrier.DENSE;
        Count step = displaced(range, carrier);
        if (step == null) {
            return List.copyOf(base);
        }
        TypeName wrapper = type instanceof Type.Ref ref
                && symbols.get(ref.name()) instanceof Ast.Data data && data.newtype()
                ? ref.name() : null;
        FixtureTemplate value = FixtureTemplate.on(carrier, step, wrapper);
        if (base.stream().anyMatch(each -> each.text().equals(value.text()))) {
            return List.copyOf(base);
        }
        base.add(value);
        return List.copyOf(base);
    }

    /** A second count of a range, or null where the carrier has none to give. */
    private static Count displaced(NumericDomain.Bounds range, Carrier carrier) {
        Count from = inside(range, carrier);
        if (from == null) {
            return null;
        }
        Endpoint min = range == null ? null : range.min();
        Endpoint max = range == null ? null : range.max();
        if (carrier.spacing() == Granularity.DENSE) {
            // No smallest step, so the only second count a range names is one inside both its ends —
            // and the one already on offer is that count where the range is open below.
            return min == null || max == null || !min.inclusive() ? null
                    : Endpoint.valueBetween(Endpoint.exclusive(min.at()), max, Granularity.DENSE);
        }
        Count up = from.plus(1);
        if (holdsCount(range, up)) {
            return up;
        }
        Count down = from.minus(1);
        return holdsCount(range, down) ? down : null;
    }

    /** Whether a range holds a count, with no range holding everything. */
    private static boolean holdsCount(NumericDomain.Bounds range, Count at) {
        return range == null || range.admits(at);
    }

    /**
     * What a newtype wraps: every value for it this can think of, in the order to try them.
     *
     * <p>Candidates, not an answer. Whether a newtype accepts a value is decided by its own
     * constructor, and this only proposes — so a rule it reads is a reason to offer another value
     * rather than to withdraw the ones already there. A format rule that cannot be read leaves the
     * position with what it had before this could read any of them, and a newtype carrying two rules
     * gets a value from each, which is why the order they are declared in does not decide whether one
     * builds.
     *
     * <p>Both the bound on a number and the format of a string, in one place, because a newtype is
     * asked for a value from two: a field of a record, and a case of a sum. Reading the rules in only
     * one of them is how a value that holds everywhere came to be written in one place and not the
     * other.
     */
    private static List<FixtureTemplate> insideTheNewtype(TypeName newtype, Symbols symbols) {
        return insideTheNewtype(newtype, symbols, null, java.util.Set.of());
    }

    private static List<FixtureTemplate> insideTheNewtype(TypeName newtype, Symbols symbols,
                                                          NumericDomain.Bounds within,
                                                          java.util.Set<TypeName> expanding) {
        // Already inside this one's own value, so the type is written in terms of itself and there is
        // nothing to hand back. Which is the answer and not a limit: no value of such a type exists.
        if (expanding.contains(newtype)) {
            return List.of();
        }
        java.util.Set<TypeName> inside = new java.util.LinkedHashSet<>(expanding);
        inside.add(newtype);
        Type base = TypeOps.newtypeInner(newtype, symbols);
        List<FixtureTemplate> candidates = new ArrayList<>();

        Bounds own = boundsOf(new Type.Ref(newtype), symbols);
        NumericDomain.Bounds bounds = admissibleBounds(own, within);
        Count held = bounds == null || bounds.isEmpty() ? null : inside(bounds, own.carrier());
        if (held != null) {
            candidates.add(FixtureTemplate.on(own.carrier(), held, null));
        }
        if (base == Type.STRING && symbols.get(newtype) instanceof Ast.Data data) {
            for (Ast.InvariantClause clause : TypeOps.effectiveInvariants(data, symbols)) {
                for (Ast.Expr each : InvariantConstraints.clauses(clause.expr())) {
                    if (InvariantConstraints.of(each, base).orElse(null)
                            instanceof InvariantConstraints.Pattern format) {
                        PatternValues.shortestAccepted(format.regex())
                                .map(FixtureTemplate::string).ifPresent(candidates::add);
                    }
                }
            }
        }
        // What the rules say the value holds, before the value that would hold nothing. A format and a
        // minimum are two proposals and not a choice between them: each is what one rule asks for, and
        // which of them the whole of the rules admits is the decoder's answer rather than an order
        // settled here.
        candidates.addAll(Witnesses.holding(base, leastHeld(new Type.Ref(newtype), symbols),
                symbols, inside));
        candidates.addAll(representativesOf(base, symbols, null, inside));

        Map<String, FixtureTemplate> once = new LinkedHashMap<>();
        for (FixtureTemplate each : candidates) {
            once.putIfAbsent(each.text(), each);
        }
        return List.copyOf(once.values());
    }

    /** A count the position holds, or null where it holds none. The ends decide it, so nothing here
     * reads one of them as a number and loses whether the range reaches it. */
    private static Count inside(NumericDomain.Bounds within, Carrier carrier) {
        if (within == null) {
            return Count.ZERO;
        }
        Count between = Endpoint.valueBetween(within.min(), within.max(), carrier.spacing());
        if (between == null) {
            return null;
        }
        // On the carrier's own grid, and then still inside. A number between two counts it can hold
        // is not always one of them (see Carrier#onTheGrid).
        Count held = carrier.onTheGrid(between);
        return held != null && within.admits(held) ? held : null;
    }

    /**
     * What a position can offer once everything it ordinarily offers has been refused.
     *
     * <p>The far edge of a range, for a position that is a bounded number. A rule relating this
     * position to another is what refuses the near one: `low < high` with `low` already fixed leaves
     * `high` a range starting at the value `low` took, and over decimals that range starts at the one
     * number the rule will not accept, because a strict bound there has no next value to step to. The
     * far edge is not knowing which number the rule wants — it is having a second number to be
     * refused at, which a range offering one edge does not.
     *
     * <p>Held back rather than offered beside the others, because what a row is searched for is the
     * product of what its positions offer and that search is bounded. A value added to one position
     * moves every assignment past it further back, so offering this one among the rest would lose
     * rows that were being reached at positions this has nothing to do with.
     */
    static List<FixtureTemplate> inReserve(Type type, Symbols symbols,
                                           NumericDomain.Bounds within) {
        if (!(type instanceof Type.Ref ref) || !(symbols.get(ref.name()) instanceof Ast.Data data)
                || !data.newtype()) {
            return List.of();
        }
        Bounds own = boundsOf(type, symbols);
        NumericDomain.Bounds bounds = admissibleBounds(own, within);
        // The far end has to be a value the position holds. Where the range stops short of it there
        // is nothing there to hold back, and a dense order has no value beside it to hold back
        // instead — what is inside is already what the first tier offers.
        if (bounds == null || bounds.min() == null || bounds.max() == null
                || !bounds.max().inclusive()
                || bounds.max().at().sameAs(bounds.min().at())) {
            return List.of();
        }
        FixtureTemplate held = FixtureTemplate.on(own.carrier(), bounds.max().at(), ref.name());
        // Nothing already on offer: a range whose far edge is the number the base type stands for
        // would otherwise hold the same value twice, once in each tier.
        return representativesOf(type, symbols, within).stream()
                .map(FixtureTemplate::text).anyMatch(held.text()::equals)
                ? List.of() : List.of(held);
    }

    private static boolean isBool(ObservedValue v, boolean expected) {
        return v instanceof ObservedValue.Bool b && b.value() == expected;
    }

    private Partitions() {}
}
