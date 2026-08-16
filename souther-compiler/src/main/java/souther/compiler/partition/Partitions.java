package souther.compiler.partition;

import souther.compiler.ast.Hir;
import souther.compiler.check.Carrier;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.HelperInvariants;
import souther.compiler.check.Shape;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.check.TypeView;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.Rules;
import souther.compiler.check.NumericMeasures;
import souther.compiler.codegen.InvariantConstraints;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.BoundaryDomain;
import souther.compiler.inputs.Membership;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.UnreadRule;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.observe.ObservedValue;
import souther.compiler.values.AdmissibleSet;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeReachName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

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
                               List<UnreadRule> unread,
                               List<BoundaryObligation> between) {
        public Partitioning {
            axes = List.copyOf(axes);
            omitted = List.copyOf(omitted);
            domains = Map.copyOf(domains);
            uncertain = java.util.Set.copyOf(uncertain);
            undivided = List.copyOf(undivided);
            unread = List.copyOf(unread);
            between = List.copyOf(between);
        }

        /** Whether an edge of this term is a value some row could carry.
         *
         * <p>False where a rule reaching the value the term is taken of was not read in full. Every
         * edge here is then where the rules this could read stop, and a rule it could not read can
         * refuse that value as easily as the one beyond it — so the edge is not known to be writable
         * and asking for a row at it is asking for work nobody may be able to do.
         *
         * <p>And false at a count, unless every count that measure could give is one some value has
         * ({@link NumericMeasures#everyCountHasAValue}). What the projection settles is which numbers
         * the rules leave, and three is a number they leave whether or not three of the thing exist:
         * a `Set<Bool>` is capped at two, and a `List<T>` of one needs a `T` that something inhabits.
         * The domain has no term for either, so such an edge is settled by a value rather than by an
         * argument — a row at it, or one this built — which is the account an edge nothing has
         * settled already gets. Read as a proof, a floor no value reaches became a row an author was
         * told to write.
         *
         * <p>A string's length is the one that stays proven, because a string of any length is
         * written by repeating a character. Declining the proof there too would take away every
         * `String.length` edge in the corpus over collections that have no values. */
        public boolean edgeIsKnownWritable(NumericTerm term) {
            return !uncertain.contains(term)
                    && !(term instanceof NumericTerm.SizeOf size
                            && !NumericMeasures.everyCountHasAValue(size.measure()));
        }

        /** Only the positions the model actually divides. */
        public List<Axis> derivable() {
            return axes.stream().filter(Axis::derivable).toList();
        }
    }

    /** The axes of one behavior. {@code sig} says the types; {@code behavior} says the parameter names,
     * which is what a path is written from. */
    public static Partitioning of(Hir.SpecBehavior behavior, Sig sig, Symbols symbols,
                                  Exclusions excluded) {
        List<Axis> found = new ArrayList<>();
        Map<NumericTerm, NumericDomain.Bounds> domains = new LinkedHashMap<>();
        java.util.Set<NumericTerm> uncertain = new java.util.LinkedHashSet<>();
        List<UnreadRule> unread = new ArrayList<>();
        for (int i = 0; i < sig.inputTypes().size() && i < behavior.params().size(); i++) {
            // One reading per parameter, not one per record met on the way down. A clause on the
            // outer record relates positions at any depth it can name, and rebuilding the reading at
            // each record is how `interval.startsAt < cap` stopped reaching `interval.startsAt`.
            Type type = sig.inputTypes().get(i);
            walk(behavior.name(), TermPath.of(behavior.params().get(i).name()), type,
                    0, symbols, found,
                    new Placed(readAs(type, symbols), rulesOf(type, symbols)),
                    domains, uncertain, unread);
        }
        found.replaceAll(axis -> axis.excluding(
                excluded.at(axis.path()).stream().map(TypeSymbol::name).toList()));
        List<Axis> kept = new ArrayList<>();
        List<OmittedAxis> omitted = new ArrayList<>();
        int counted = 0;
        for (Axis axis : found) {
            if (!axis.measurable()) {
                kept.add(axis);   // kept so a report can name what it could not measure
            } else if (counted < MAX_AXES) {
                kept.add(axis);
                counted++;
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
        // compares it. Nothing has compared anything yet, so what the rules came to is whether one
        // of them was left unread — settled beside each axis, as it is once a body has spoken.
        List<Measured> measured = new ArrayList<>();
        for (Axis axis : kept) {
            keep(new ArrayList<>(), measured, axis, null, unread);
        }
        return new Partitioning(kept, omitted, domains, uncertain, undividedIn(measured),
                List.copyOf(unread), List.of());
    }

    /**
     * The positions with no classes, each saying which of the two it is.
     *
     * <p>Derived from the axes rather than recorded beside them, so that a position measured after a
     * threshold arrives leaves this list by the same rule it entered it. {@code stopped} names the
     * ones the walk did not finish, which is the one thing the axes cannot say for themselves: an
     * axis that was never descended into looks exactly like one there was nothing under.
     */
    /**
     * One position, and what the rules written about it came to.
     *
     * <p>Paired where both are in hand rather than rejoined afterwards by how a path is spelled.
     * What holds the two to one position is {@link #keep} making them together — the type says they
     * travel together, not that they are of the same position — and that is the whole of the
     * difference from a list of reasons matched to a list of positions later.
     */
    private record Measured(Axis axis, BodyCutInspection body) {}

    /** The axis, and the body's answer about it — a line it drew, nothing, or a rule about it that
     *  went unread. Kept beside the axis rather than looked up afterwards by how its path is
     *  spelled. */
    private static void keep(List<Axis> out, List<Measured> measured, Axis axis,
                             BodyCutInspection drew, List<UnreadRule> rules) {
        out.add(axis);
        if (drew != null) {
            measured.add(new Measured(axis, drew));
            return;
        }
        BlockReason unread = rules.stream().filter(one -> one.at().equals(axis.path()))
                .map(UnreadRule::why).findFirst().orElse(null);
        measured.add(new Measured(axis, unread == null ? new BodyCutInspection.Exhausted()
                : new BodyCutInspection.Blocked(unread)));
    }

    /**
     * What each position is left with, folded from the two readings that were made of it.
     *
     * <p>Nothing is searched for here. Both answers were settled where the position was read — the
     * structural one on the axis, the rules' one beside it — and this only says which of them a
     * report is owed, so a reason recovered here by matching a path would be a reading happening
     * twice.
     *
     * <p>The structural reason outranks the rules': where the walk could not reach into what the
     * position holds, a rule naming something inside it is a second description of that same stop
     * and the first is the cause (issue #626).
     */
    private static List<UndividedPosition> undividedIn(List<Measured> measured) {
        List<UndividedPosition> out = new ArrayList<>();
        for (Measured each : measured) {
            PendingPosition pending = PendingPosition.of(each.axis());
            if (pending != null) {
                out.add(pending.complete(each.body()));
            }
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
        return withThresholds(base, thresholds, symbols, unread, singled, List.of());
    }

    /**
     * The same, with the lines a body draws between two of its positions.
     *
     * <p>Carried through rather than derived here. A line between two positions divides neither of
     * them, so nothing about it belongs to an axis — it is read where the comparison is and travels
     * beside the partition, which is what keeps a position the classes could say nothing about from
     * losing the line its body draws about it.
     */
    public static Partitioning withThresholds(Partitioning base, List<Threshold> thresholds,
                                              Symbols symbols,
                                              List<UnreadRule> unread,
                                              List<GuardThresholds.Guards.Singled> singled,
                                              List<BoundaryObligation> between) {
        // Both producers of one kind of evidence. What a body compared and what a type's own rules
        // bound are read by different readers and answer the same question, so a position either of
        // them wrote about and neither could turn into a line is named once, whichever wrote it.
        List<UnreadRule> rules = new ArrayList<>(base.unread());
        for (UnreadRule each : unread) {
            if (rules.stream().noneMatch(had -> had.equals(each))) {
                rules.add(each);
            }
        }
        List<Axis> out = new ArrayList<>();
        List<Measured> measured = new ArrayList<>();
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
                NumericTerm at = term;
                Axis here2 = axis;
                keep(out, measured, refine(axis,
                        () -> singledClasses(points, at, here2.type(), only, symbols),
                        mergedPoints(axis.cuts(), points, at.carrierAt(axis.type(), symbols))),
                        new BodyCutInspection.Evidence(), rules);
                continue;
            }
            if (here.isEmpty()) {
                // A position no rule divides, whose body measures some other number of it: a bare
                // `List<String>` nothing bounds, under a `guard List.length(t.names) > 0`. The line
                // is on that number, so the axis becomes one about it — there was nothing else here
                // for it to be about, and dropping the threshold would lose a line the body draws.
                NumericTerm drawn = axis.measurable() ? null : soleTermAt(thresholds, axis.path());
                if (drawn == null) {
                    keep(out, measured, axis, null, rules);
                    continue;
                }
                term = drawn;
                here = thresholds.stream().filter(t -> t.term().equals(drawn)).toList();
                axis = axis.measuredAt(new AxisId(axis.id().behavior(), drawn.toString()), drawn);
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
            // Through `excluding`, so that a class list replaced by the intervals a threshold cuts
            // keeps only the exclusions it still has classes for.
            //
            // A rule read and left outside what the position holds divided nothing, and it is not
            // a rule that went unread either: what it says was understood. So the answer there is
            // that the rules were exhausted, which is what keeps `Blocked` meaning that a
            // comparison could not be interpreted rather than everything that came to nothing.
            NumericDomain.Bounds within = domain;
            NumericTerm measuredAt = term;
            Axis read = axis;
            keep(out, measured, refine(axis.measuredAt(axis.id(), term),
                    () -> Intervals.classesOf(
                            Intervals.of(reachable, within == null ? null : within.min(),
                                    within == null ? null : within.max()),
                            measuredAt, read.type(), symbols),
                    merged(axis.cuts(), reachable, carrier)),
                    reachable.isEmpty() ? null : new BodyCutInspection.Evidence(), rules);
        }
        return new Partitioning(out, base.omitted(), domainsOf(base, out), base.uncertain(),
                undividedIn(measured), List.copyOf(rules), between);
    }

    /**
     * The same position, with what a body's rules add to it.
     *
     * <p>Refinement and not replacement. What a body draws is evidence arriving after the model's
     * own, and evidence only ever tells a position's values apart more finely — so where the model
     * already divides the position, the lines a body draws are lines among those classes and the
     * classes stay as they are. Rebuilt from the lines, a position the model divides three ways
     * would come back divided two ways, and the loss reads as the model never having stated the
     * third.
     *
     * <p>Which is a rule about the classes and not about the carrier. It stood as a test for an
     * enumeration, being where it was first noticed; a position whose rules name the values it
     * holds is divided just as finely and had no such test, so a {@code guard} over it replaced
     * what the model states.
     *
     * <p>The two agree wherever the old one fired, and they agree by construction rather than by
     * luck: an enumeration's cases are its classes, and a crossing never leaves a position whose
     * type states classes without any ({@code LocalInspection}'s {@code constructibleAt}). So there
     * is no position with an ordered carrier for these to be about, and ranges over the count an
     * enumeration's cases are ordered by are never rebuilt into a partition of them.
     *
     * <p>The lines are taken either way. A line is still a line where it divides nothing new, and
     * still owes its rows.
     *
     * @param otherwise the classes to use where the model divides the position no way, asked for
     *                  only there — a position that already has classes has no use for them, and
     *                  working them out would be a reading whose answer is thrown away
     */
    private static Axis refine(Axis axis, java.util.function.Supplier<List<PartitionClass>> otherwise,
                               List<Cut> cuts) {
        return axis.carrying(axis.derivable() ? axis.classes() : otherwise.get(), cuts);
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
        List<Place> values = new ArrayList<>();
        for (GuardThresholds.Guards.Singled each : points) {
            if (values.stream().noneMatch(had -> had.sameAs(each.value()))) {
                values.add(each.value());
            }
        }
        List<PartitionClass> classes = new ArrayList<>();
        for (Place value : values) {
            String written = carrier.written(value);
            classes.add(classAt(term + "/= " + written, "= " + written,
                    holding(term, carrier, at -> at.sameAs(value)),
                    standing(type, carrier, value, symbols)));
        }
        Place other = carrier.somethingOtherThan(values, within);
        String label = "/= " + String.join(", ",
                values.stream().map(carrier::written).toList());
        classes.add(other == null
                ? PartitionClass.ungeneratable(term + "/" + label, label,
                        holding(term, carrier, at -> values.stream().noneMatch(at::sameAs)),
                        "nothing here composed a value of this position other than the ones"
                                + " singled out")
                : classAt(term + "/" + label, label,
                        holding(term, carrier, at -> values.stream().noneMatch(at::sameAs)),
                        standing(type, carrier, other, symbols)));
        return List.copyOf(classes);
    }

    /** A class over the one value that stands for it, or one nothing produces where there is no
     *  such value — which is what a position wearing a name this module cannot write leaves. */
    private static PartitionClass classAt(String id, String label, Classifier is,
                                          FixtureTemplate standing) {
        return standing == null
                ? PartitionClass.ungeneratable(id, label, is,
                        "nothing here can write a value of this position")
                : PartitionClass.of(id, label, is, RepresentativeSource.of(standing));
    }

    /** A count written at a position, wearing every name that position declares. */
    private static FixtureTemplate standing(Type type, Carrier carrier, Place at, Symbols symbols) {
        return Witnesses.wrapped(type, FixtureTemplate.on(carrier, at, symbols.scope()::reach), symbols);
    }

    /** A classifier that reads the term's count out of a row and answers about it. */
    private static Classifier holding(NumericTerm term, Carrier carrier,
                                      java.util.function.Predicate<Place> holds) {
        return value -> switch (term.read(value, carrier)) {
            case NumericTerm.Reading.Number number -> Membership.of(holds.test(number.value()));
            case NumericTerm.Reading.Missing missing -> new Membership.Incomplete(missing.code());
            case NumericTerm.Reading.NotNumber _ -> Membership.NO_MATCH;
        };
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
     * A place both positions of a line between them can hold, or null where their rules leave none.
     *
     * <p>What proves a row can be written on such a line. The line is where the two positions are
     * equal, so a row on it writes one place at both — and whether one exists is the two positions'
     * ranges read together, which is a question the rules answer without anything being built.
     *
     * <p>Which place a pair of ends gives up is {@link Carrier#somethingInside}'s single rule, so a
     * range open at both ends answers the same way here as anywhere else, and a carrier whose values
     * are strings answers it the way a carrier whose values count does.
     *
     * <p>Null is not a proof of the opposite. Two ranges that leave no place leave none, and that is a
     * fact about the rules; a range this could not read in full is a range this did not read, and the
     * caller is the one holding whether that happened.
     */
    public static Place commonPlace(Map<NumericTerm, NumericDomain.Bounds> domains,
                                    BoundaryTarget.EqualTerms line) {
        NumericDomain.Bounds on = domains.get(line.on());
        NumericDomain.Bounds against = domains.get(line.against());
        Endpoint min = Endpoint.lower(on == null ? null : on.min(),
                against == null ? null : against.min());
        Endpoint max = Endpoint.upper(on == null ? null : on.max(),
                against == null ? null : against.max());
        return line.carrier().somethingInside(min, max);
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
                    out.add(new BoundaryObligation(
                            new BoundaryTarget.AtPlace(axis.id(), cut.carrier(), cut.at()),
                            origin, BoundaryObligation.BoundarySide.AT));
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
                                        new BoundaryTarget.AtPlace(axis.id(), cut.carrier(), next),
                                        origin, BoundaryObligation.BoundarySide.ABOVE)));
                    } else {
                        domain.predecessor(cut.at())
                                .filter(before -> within == null || within.admits(before))
                                .ifPresent(before -> out.add(new BoundaryObligation(
                                        new BoundaryTarget.AtPlace(axis.id(), cut.carrier(), before),
                                        origin, BoundaryObligation.BoundarySide.BELOW)));
                    }
                }
            }
        }
        return List.copyOf(out);
    }

    /**
     * One position, answered by the phases in the order that decides it.
     *
     * <p>The local reading first, whole: the classes the type states and the lines its rules draw
     * come back as one answer, so what "local evidence ran out" means is a value rather than two
     * empty lists to be noticed. Only where it ran out is the position asked what it is made of —
     * a position its own type answered for is not descended into, whatever is under it, and that
     * precedence is the arm this is written in rather than the order of two {@code if}s.
     *
     * <p>Of the structural answers only {@code Children} takes the position away: the walk goes on
     * without it, and the classes belong to what is underneath. A leaf and a block both leave the
     * position standing, pending what a body's rules say later.
     *
     * <p><b>A position with local evidence and children is intended and unreachable today.</b> Only
     * a product has children, and a product carries neither classes — its type states no division —
     * nor cuts, having no order for a rule to name a value on. So which of the two wins is a
     * decision about a state the language cannot currently be in. It is written as a decision all
     * the same: a field-level partition, a guard-derived class on a record, or an invariant over a
     * whole product would inhabit it, and an implementation that descended because the position is
     * structural would then lose evidence it had already read.
     */
    private static void walk(String behavior, TermPath path, Type type, int depth, Symbols symbols,
                             List<Axis> out, Placed placed,
                             Map<NumericTerm, NumericDomain.Bounds> domains,
                             java.util.Set<NumericTerm> uncertain, List<UnreadRule> unread) {
        // Once, and every phase asks of this reading: what the position's own type and rules say,
        // and what is under it where they say nothing, are two questions put to one reading of it.
        //
        // The proof first, and before anything is read off the position. A shape a partition is not
        // derived from is this compiler disagreeing with itself about what may stand at a position,
        // and it is refused here — asked after the local phase instead, a position that produced
        // classes was never checked at all, and the one case the type exists to make loud was the
        // one that stayed quiet.
        PartitionInput input = PartitionInput.of(TypeView.of(type, symbols));
        LocalInspection inspected = LocalInspection.of(input, path, symbols, placed);
        LocalReading reading = inspected.reading();
        for (UnreadRule each : reading.unread()) {
            if (unread.stream().noneMatch(had -> had.equals(each))) {
                unread.add(each);
            }
        }
        NumericTerm term = reading.term();
        AxisId id = AxisId.of(behavior, term);
        if (reading.admissible() != null && !reading.admissible().isEmpty()) {
            domains.put(term, reading.admissible());
        }
        switch (inspected.partition()) {
            case LocalPartition.Divided divided -> {
                if (divided.cuts() instanceof CutEvidence.Present drawn && drawn.uncertain()) {
                    uncertain.add(term);
                }
                out.add(new Axis(id, term, type, divided.classes(), divided.cuts().cuts(),
                        java.util.Set.of(), divided.completeness(), null, null));
            }
            // Nothing local divides the position, which is what licenses asking what is under it.
            // Whether the reading got to the end of the rules is carried rather than acted on here:
            // a position made of positions is given up in favour of what is under it either way,
            // and a rule about the whole value that this could not read says nothing about which of
            // its fields it would have divided.
            case LocalPartition.Open _, LocalPartition.Blocked _ -> {
                switch (StructuralInspection.of(input.shape(), depth < MAX_DEPTH)) {
                    // The one answer that takes the position away: what is under it is what the
                    // classes belong to, and this position is not carried further.
                    case StructuralInspection.Children children -> {
                        for (Map.Entry<String, Type> field : children.under().entrySet()) {
                            walk(behavior, path.then(field.getKey()), field.getValue(), depth + 1,
                                    symbols, out, placed, domains, uncertain, unread);
                        }
                    }
                    // A leaf and a block are both positions still to be answered for, and each
                    // carries what it is left with if nothing answers — including a rule about this
                    // position that the local reading could not take in, which is what keeps the
                    // position from completing as one the model divides no way.
                    case StructuralInspection.Pending pending ->
                            out.add(Axis.pendingAt(id, term, type,
                                    reading.admitted().completeness(), pending,
                                    inspected.partition() instanceof LocalPartition.Blocked blocked
                                            ? blocked.why() : null));
                }
            }
        }
    }


    /** The value a position is inside: what it is called, and what its rules leave each position of
     * it able to hold. */
    record Placed(TypeSymbol value, Rules rules) {

        /** What the rules leave the numbers, ends and narrowings of this value. */
        FieldDomains bounds() {
            return rules.bounds();
        }

        /** What is left for the position at {@code path}, which is read from the value this is of. */
        NumericDomain.Bounds at(TermPath path) {
            return path.fields().isEmpty() ? null
                    : bounds().at(String.join(".", path.fields()));
        }

        /**
         * Which values the position at {@code path} may hold, and how much of its rules was read.
         *
         * <p>Asked at every path, the value's own included: what a name wraps is at no path of its
         * own and is the position a reader of a newtype asks about, which is why this is not the
         * empty answer where {@link #at} is.
         */
        AdmissibleSet admits(TermPath path) {
            return rules.admits(String.join(".", path.fields()));
        }

        /** The ends the clauses reaching this value place on the coordinates at {@code path}, which
         * is a different question from what {@link #at} leaves them. */
        List<FieldDomains.Placed> placedAt(TermPath path) {
            return path.fields().isEmpty() ? List.of()
                    : bounds().placedAt(String.join(".", path.fields()));
        }

        /** Which declarations' clauses are holding the end at {@code path}, on the side asked for. */
        List<TypeSymbol> narrowedBy(TermPath path, boolean lower) {
            return path.fields().isEmpty() ? List.of()
                    : bounds().narrowedBy(String.join(".", path.fields()), lower);
        }
    }

    /** The record a position holds, through the names it is written under: a value of
     *  {@code data SlotN = Slot} is a {@code Slot}, and the clauses relating its fields are
     *  {@code Slot}'s. */
    private static TypeSymbol recordIn(Type type, Symbols symbols) {
        return TypeView.of(type, symbols).shape() instanceof Shape.Product product
                ? product.name() : null;
    }

    /**
     * What the record a field sits in leaves each of its fields able to hold.
     *
     * <p>Of the record, and not of a name written over it. A clause relating two fields is written
     * on the declaration that has them, so a position of {@code data PairN = Pair} is bounded by
     * {@code Pair}'s clauses — read off the written name, the walk descended into the fields of a
     * record whose rules about them it had just dropped.
     */
    /**
     * What the rules reaching a value of {@code type} leave and place, read under the name the
     * signature wrote.
     *
     * <p>The written name and not the record under it. A name wrapped round a record is a place the
     * same rule can be written — {@code data NonEmptyBag = Bag invariant List.length(value.xs) >= 1}
     * states what {@code Bag} could have stated about its own field — and reading the record alone
     * drops every clause of every name round it. What those clauses leave is read at the paths the
     * record's own positions have, since a name wrapped round a value is not a step of the path.
     *
     * <p>One reading and not two. A wrapper's clauses place ends, project ranges onto the record's
     * fields, and can be ones this could not read, and all three are answers about the same value:
     * lifted as ends alone, a wrapper relating two of the record's fields narrowed nothing and a
     * wrapper clause nothing could read left every edge under it looking certain.
     *
     * <p>Whether there was a declaration to read at all is {@link Rules}' answer and not a default
     * this fills in. A position with no declaration on it has no rule written about it, and a
     * reading that said instead "a rule about this may have gone unread" would say it of every
     * plain {@code String} in every model.
     */
    private static Rules rulesOf(Type type, Symbols symbols) {
        return Rules.of(readAs(type, symbols), symbols);
    }

    /**
     * The declaration a value of {@code type} is read under: the name the signature wrote where it
     * names one, and the record beneath the names where it does not.
     *
     * <p>One name for both questions. Which declaration's rules reach the positions, and which
     * declaration is said to have taken an edge in, are answers about the same value — read apart,
     * an edge a wrapper narrowed was reported as narrowed by the record under it, which is a
     * declaration that may have no clause about the pair at all.
     */
    private static TypeSymbol readAs(Type type, Symbols symbols) {
        TypeSymbol written = nameOf(type);
        return written != null && symbols.declarations().declaration(written.key()) instanceof Hir.Data ? written
                : heldIn(type, symbols);
    }

    /**
     * The declaration whose rules reach the position: the record under the names where there is
     * one, and the declaration as written where there is not.
     *
     * <p>A position that is not a record has no fields for a clause to relate, and its own rules
     * still say what a reading of them could not turn into a range — which is what keeps an edge it
     * refuses from being called writable. So the answer falls back to the name the signature wrote
     * rather than to nothing.
     */
    private static TypeSymbol heldIn(Type type, Symbols symbols) {
        TypeSymbol record = recordIn(type, symbols);
        return record != null ? record : nameOf(type);
    }

    private static TypeSymbol nameOf(Type type) {
        return type instanceof Type.Ref ref ? ref.name() : null;
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
                                                   java.util.Set<TypeSymbol> expanding) {
        if (type == null) {
            return List.of();
        }
        if (type == Type.INT || type == Type.DECIMAL) {
            Carrier carrier = type == Type.DECIMAL ? Carrier.DENSE : Carrier.WHOLE;
            Place at = inside(within, carrier);
            FixtureTemplate standing = at == null ? null
                    : FixtureTemplate.on(carrier, at, symbols.scope()::reach);
            return standing == null ? List.of() : List.of(standing);
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
        if (type == Type.TIME) {
            return List.of(FixtureTemplate.time("00:00:00"));
        }
        if (type == Type.DATETIME) {
            return List.of(FixtureTemplate.dateTime("2000-01-01T00:00:00"));
        }
        if (type == Type.INSTANT) {
            return List.of(FixtureTemplate.instant("2000-01-01T00:00:00Z"));
        }
        // The empty one, for every collection nothing has said otherwise about. A row whose collection
        // is not what it is about should say so by carrying nothing, and where no rule counts what the
        // position holds there is nothing else to go on. What a rule does say is read a layer out, at
        // the newtype the rule is written on.
        if (type instanceof Type.ListOf || type instanceof Type.SetOf || type instanceof Type.MapOf) {
            return List.of(FixtureTemplate.emptyCollection());
        }
        // Absence, which every optional holds. Answered here rather than through the classes below
        // because what the classes say about `Some` is what stands for the element, and asking that
        // while the element is being built is the element asking for itself.
        if (type instanceof Type.OptionOf) {
            return List.of(FixtureTemplate.none());
        }
        List<PartitionClass> classes = PartitionClasses.of(type, symbols);
        for (PartitionClass each : classes) {
            List<FixtureTemplate> stands = standingFor(each.representatives(), symbols, expanding);
            if (!stands.isEmpty()) {
                return stands;
            }
        }
        // Where there were classes, they have answered. Each said nothing can be produced for it and
        // why, and reading that and then arriving at a value another way is this deciding the classes
        // were wrong about themselves — the answer they carry is the one an author is shown.
        if (!classes.isEmpty()) {
            return List.of();
        }
        // A newtype the model only bounds has no classes — everything outside the bound is refused at
        // construction — but it does have values, and the edge of the bound is one that builds.
        if (type instanceof Type.Ref ref && symbols.declarations().declaration(ref.name().key()) instanceof Hir.Data data) {
            if (!data.newtype()) {
                return composed(ref.name(), symbols, expanding);
            }
            // A newtype nothing here names has no value anything here can write: the name goes on
            // the value as it is written, and there is none to put on.
            return symbols.scope().reach(ref.name()) instanceof TypeReachName.Written written
                    ? insideTheNewtype(ref.name(), symbols, within, expanding).stream()
                            .map(t -> FixtureTemplate.newtype(written, t)).toList()
                    : List.of();
        }
        return List.of();
    }

    /**
     * The values a recipe arrives at, whichever way it arrives at them.
     *
     * <p>{@code Values} and {@code Compose} are two ways of writing where a representative comes
     * from and not two answers about whether there is one, so a reader asking for one takes both
     * here. Read as a reader's own two questions — is it generatable, and does it hold values — a
     * class naming a constructor answered yes and then handed over nothing, and the position it
     * stood at was reported as one no value can be written at (issue #651).
     */
    static List<FixtureTemplate> standingFor(RepresentativeSource source, Symbols symbols,
                                             java.util.Set<TypeSymbol> expanding) {
        return switch (source.evaluate()) {
            case RepresentativeSource.Evaluation.Values values -> values.written();
            case RepresentativeSource.Evaluation.Compose compose ->
                    composed(compose.through(), symbols, expanding).stream()
                            .map(compose::written).toList();
            case RepresentativeSource.Evaluation.NothingProducible _ -> List.of();
        };
    }

    /**
     * A record composed field by field, or nothing where one of its fields has nothing to stand for
     * it.
     *
     * <p>{@code expanding} carries the names this is already inside the value of, so a record
     * reached from its own field is given up on there rather than composed forever. Path-local: a
     * name is in it only while the value under it is being built, so a type met twice in two
     * branches is composed in both.
     *
     * <p>Each field is chosen against what the record's rules leave it, which is the reading
     * {@link FieldDomains} makes of them: the range a clause leaves the value, and the floor a
     * clause counting it puts on what it holds. Chosen from the field's type alone, a record whose
     * rule asks its list for two is handed one holding none, and the row it was composed for comes
     * back as one every value tried was refused at.
     *
     * <p>Nothing about the clauses relating two fields, which are read where a row is searched for
     * one position at a time. Whether the values may be held together is the decoder's answer — the
     * same answer every other candidate this offers is put through.
     */
    private static List<FixtureTemplate> composed(TypeSymbol record, Symbols symbols,
                                                  java.util.Set<TypeSymbol> expanding) {
        if (expanding.contains(record) || !(symbols.declarations().declaration(record.key()) instanceof Hir.Data data)) {
            return List.of();
        }
        Map<String, Type> fields = TypeOps.fieldTypes(data, symbols);
        if (fields.isEmpty()) {
            return List.of();   // a unit has no fields to compose, and is named rather than built
        }
        java.util.Set<TypeSymbol> inside = new LinkedHashSet<>(expanding);
        inside.add(record);
        Map<String, Count> settled = new LinkedHashMap<>();
        FieldDomains left = FieldDomains.of(record, data, symbols, settled);
        Map<String, FixtureTemplate> chosen = new LinkedHashMap<>();
        for (Map.Entry<String, Type> field : fields.entrySet()) {
            List<FixtureTemplate> stands = representativesHolding(field.getValue(), symbols,
                    left.at(field.getKey()), left.heldAt(field.getKey()), inside);
            if (stands.isEmpty()) {
                return List.of();
            }
            FixtureTemplate at = stands.get(0);
            chosen.put(field.getKey(), at);
            // Settled, and the rules read again with it in them. A field chosen against the rules as
            // they stand before anything is settled is chosen against `a < b` with `a` still open,
            // which leaves `b` its whole range and takes the bottom of it.
            if (Counts.writtenIn(at.value()) instanceof Count count) {
                settled.put(field.getKey(), count);
                left = FieldDomains.of(record, data, symbols, settled);
            }
        }
        return symbols.scope().reach(record) instanceof TypeReachName.Written written
                ? List.of(FixtureTemplate.record(written, chosen)) : List.of();
    }

    /** How many of whatever counts a value the rules on it require it to hold, read where the rules
     * are: {@link DeclaredBounds#leastCountOf}. */
    static int leastHeld(Type type, Symbols symbols) {
        return DeclaredBounds.leastCountOf(type, symbols);
    }

    /** The same, where the record the position sits in has a rule about it too. */
    static int leastHeld(Type type, Symbols symbols, FieldDomains.Held held) {
        return DeclaredBounds.leastCountOf(type, symbols, held);
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
     *
     * <p>{@code held} for the same reason {@link #representativesHolding} takes one: the floor this
     * reads is the floor that was built against, and a reading here that knew only the type would
     * say "every value tried was refused" of a position whose values were never built.
     */
    static Generator.UnresolvedCombination.Reason notBuilt(Type type, Symbols symbols,
                                                            FieldDomains.Held held) {
        return Witnesses.heldBackFor(TypeOps.base(type, symbols), leastHeld(type, symbols, held),
                symbols);
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
    static Place numberInside(Type type, Symbols symbols, int index) {
        Type base = TypeOps.numericBase(type, symbols);
        if (base == null) {
            return null;
        }
        NumericDomain.Bounds range = TypeBounds.admissible(DeclaredBounds.of(type, symbols), null);
        Place from = inside(range, base == Type.DECIMAL ? Carrier.DENSE : Carrier.WHOLE);
        if (from == null || base != Type.INT) {
            return from != null && index == 0 ? from : null;
        }
        Count stepped = Count.number(from).plus(index);
        return holdsCount(range, stepped) ? stepped : null;
    }

    /**
     * The same, with what a floor asks for offered ahead of it.
     *
     * <p>Both, and the floor first. Each is what one rule was read to produce and which of them the
     * whole of the rules admits is the decoder's answer, so neither withdraws the other — the same
     * reading {@link #insideTheNewtype} makes of a newtype carrying a floor, made here of a position
     * whose floor is its record's. What the order decides is not which is right: the search over a
     * row's positions is bounded, so a position offering the value that holds nothing first spends
     * an assignment on a value the rule refuses, and rows at positions the rule has nothing to do
     * with are what runs out.
     */
    static List<FixtureTemplate> representativesHolding(Type type, Symbols symbols,
                                                        NumericDomain.Bounds within,
                                                        FieldDomains.Held held) {
        return representativesHolding(type, symbols, within, held, java.util.Set.of());
    }

    /** The same, with the names this is already inside the value of, for the same reason
     *  {@link #representativesOf} carries them. */
    static List<FixtureTemplate> representativesHolding(Type type, Symbols symbols,
                                                        NumericDomain.Bounds within,
                                                        FieldDomains.Held held,
                                                        java.util.Set<TypeSymbol> expanding) {
        List<FixtureTemplate> candidates = new ArrayList<>();
        // Under every name the position wears, because a floor read off the record says how much the
        // value holds and not what it is written as: a field of a newtype over a list takes a list
        // inside that newtype's own name.
        for (FixtureTemplate bare : Witnesses.holding(TypeOps.base(type, symbols),
                leastHeld(type, symbols, held), symbols, expanding)) {
            candidates.add(Witnesses.wrapped(type, bare, symbols));
        }
        candidates.addAll(representativesOf(type, symbols, within, expanding));
        Map<String, FixtureTemplate> once = new LinkedHashMap<>();
        for (FixtureTemplate each : candidates) {
            once.putIfAbsent(each.text(), each);
        }
        return List.copyOf(once.values());
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
                                                            NumericDomain.Bounds within,
                                                            FieldDomains.Held held) {
        List<FixtureTemplate> base =
                new ArrayList<>(representativesHolding(type, symbols, within, held));
        // What a position holds back for the product search's second pass is on offer here from the
        // start. This pass runs only where both of those have already failed, and a position keeping
        // a value from the last search there is a value nothing will ever be tried at.
        for (FixtureTemplate kept : inReserve(type, symbols, within)) {
            if (base.stream().noneMatch(each -> each.text().equals(kept.text()))) {
                base.add(kept);
            }
        }
        Type numeric = TypeOps.numericBase(type, symbols);
        if (numeric == null) {
            return List.copyOf(base);
        }
        NumericDomain.Bounds range = TypeBounds.admissible(DeclaredBounds.of(type, symbols), within);
        Carrier carrier = numeric == Type.INT ? Carrier.WHOLE : Carrier.DENSE;
        Place step = displaced(range, carrier);
        if (step == null) {
            return List.copyOf(base);
        }
        FixtureTemplate value = standing(type, carrier, step, symbols);
        if (base.stream().anyMatch(each -> each.text().equals(value.text()))) {
            return List.copyOf(base);
        }
        base.add(value);
        return List.copyOf(base);
    }

    /** A second count of a range, or null where the carrier has none to give. */
    private static Place displaced(NumericDomain.Bounds range, Carrier carrier) {
        Place from = inside(range, carrier);
        if (from == null) {
            return null;
        }
        Endpoint min = range == null ? null : range.min();
        Endpoint max = range == null ? null : range.max();
        if (carrier.spacing() == Granularity.DENSE) {
            // No smallest step, so the only second count a range names is one inside both its ends —
            // and the one already on offer is that count where the range is open below.
            return min == null || max == null || !min.inclusive() ? null
                    : carrier.somethingInside(Endpoint.exclusive(min.at()), max);
        }
        Count up = Count.number(from).plus(1);
        if (holdsCount(range, up)) {
            return up;
        }
        Count down = Count.number(from).minus(1);
        return holdsCount(range, down) ? down : null;
    }

    /** Whether a range holds a count, with no range holding everything. */
    private static boolean holdsCount(NumericDomain.Bounds range, Place at) {
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
    static List<FixtureTemplate> insideTheNewtype(TypeSymbol newtype, Symbols symbols) {
        return insideTheNewtype(newtype, symbols, null, java.util.Set.of());
    }

    static List<FixtureTemplate> insideTheNewtype(TypeSymbol newtype, Symbols symbols,
                                                          NumericDomain.Bounds within,
                                                          java.util.Set<TypeSymbol> expanding) {
        // Already inside this one's own value, so the type is written in terms of itself and there is
        // nothing to hand back. Which is the answer and not a limit: no value of such a type exists.
        if (expanding.contains(newtype)) {
            return List.of();
        }
        java.util.Set<TypeSymbol> inside = new java.util.LinkedHashSet<>(expanding);
        inside.add(newtype);
        Type base = TypeOps.newtypeInner(newtype, symbols);
        List<FixtureTemplate> candidates = new ArrayList<>();

        DeclaredBounds.Bounds own = DeclaredBounds.of(new Type.Ref(newtype), symbols);
        NumericDomain.Bounds bounds = TypeBounds.admissible(own, within);
        Place held = bounds == null || bounds.isEmpty() ? null : inside(bounds, own.carrier());
        FixtureTemplate at = held == null ? null
                : FixtureTemplate.on(own.carrier(), held, symbols.scope()::reach);
        if (at != null) {
            candidates.add(at);
        }
        if (base == Type.STRING && symbols.declarations().declaration(newtype.key()) instanceof Hir.Data data) {
            for (Hir.InvariantClause clause : TypeOps.effectiveInvariants(data, symbols)) {
                for (Hir.Expr each : HelperInvariants.conjunctsOf(clause.expr())) {
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
    private static Place inside(NumericDomain.Bounds within, Carrier carrier) {
        if (within == null) {
            return Count.ZERO;
        }
        Place between = carrier.somethingInside(within.min(), within.max());
        if (between == null) {
            return null;
        }
        // On the carrier's own grid, and then still inside. A number between two counts it can hold
        // is not always one of them (see Carrier#onTheGrid).
        Place held = carrier.onTheGrid(between);
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
        if (!(type instanceof Type.Ref ref) || !(symbols.declarations().declaration(ref.name().key()) instanceof Hir.Data data)
                || !data.newtype()) {
            return List.of();
        }
        DeclaredBounds.Bounds own = DeclaredBounds.of(type, symbols);
        NumericDomain.Bounds bounds = TypeBounds.admissible(own, within);
        // The far end has to be a value the position holds. Where the range stops short of it there
        // is nothing there to hold back, and a dense order has no value beside it to hold back
        // instead — what is inside is already what the first tier offers.
        if (bounds == null || bounds.min() == null || bounds.max() == null
                || !bounds.max().inclusive()
                || bounds.max().at().sameAs(bounds.min().at())) {
            return List.of();
        }
        FixtureTemplate held = standing(type, own.carrier(), bounds.max().at(), symbols);
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
