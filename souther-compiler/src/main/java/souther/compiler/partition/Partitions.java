package souther.compiler.partition;

import souther.compiler.check.ReadingPolicy;
import souther.compiler.ast.Hir;
import souther.compiler.check.Carrier;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.ClauseHelpers;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.NumericMeasures;
import souther.compiler.codegen.InvariantConstraints;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.StructuralInspection;
import souther.compiler.inputs.TypeBounds;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.UnreadRule;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
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

    /**
     * What the model divides one behavior into: every position, every line, and what the reading
     * that produced them could not settle.
     *
     * <p><b>What it is, and nothing about who read it.</b> The reading of the declarations is what
     * this is worked out from, and it used to be carried here as well — so the geometry compared by
     * which reading had built it, and could not be an answer this compiler keeps. It is one now, and
     * the reading is handed to the few places that go on asking it further questions.
     *
     * @param axes the positions this behavior is measured at, in parameter order. Every position
     *             the model divides is one of them: what a behavior is measured at is settled by
     *             what its types say and by what its body compares, and a count of positions is
     *             not a measure of what any of that costs (see this package's documentation)
     */
    public record Partitioning(List<Axis> axes,
                               java.util.Set<NumericTerm> uncertain,
                               List<UndividedPosition> undivided,
                               List<UnreadRule> unread,
                               List<souther.compiler.inputs.PositionReadingBlocked> blocked,
                               List<souther.compiler.inputs.PositionValuesNotSeparated> notSeparated,
                               List<Border> between,
                               List<GuardThresholds.Guards.AtAPosition> compared,
                               ReachingCuts reaching,
                               MeasureClosure.OfThePartition partitionClosure,
                               MeasureClosure.OfTheBorder borderClosure) {
        public Partitioning {
            compared = List.copyOf(compared);
            axes = List.copyOf(axes);
            uncertain = java.util.Set.copyOf(uncertain);
            undivided = List.copyOf(undivided);
            unread = List.copyOf(unread);
            blocked = List.copyOf(blocked);
            notSeparated = List.copyOf(notSeparated);
            between = List.copyOf(between);
            // Made where the reading is, never here. A closure this constructor could compute would
            // be one a caller assembling a `Partitioning` by hand could also have written, and
            // `Closed` is a conclusion about a reading rather than a shape of the lists beside it.
            if (partitionClosure == null || borderClosure == null) {
                throw new IllegalArgumentException(
                        "a partitioning with no account of what each measure's reading came to");
            }
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


    /**
     * The same, reading the input's rules here.
     *
     * <p>For a caller that has no reading of them in hand. The pipeline that measures a behavior
     * reads them once and hands the same one to everything that asks, since each of these reading
     * its own is every rule of every parameter read again to arrive at the same answers.
     */
    public static Partitioning of(String behavior, InputDomain inputs, Symbols symbols,
                                  ReadingPolicy policy) {
        return of(behavior, inputs, inputs.quantities(symbols), symbols, policy);
    }

    /**
     * The axes of one behavior, derived from the one reading of its input.
     *
     * <p>Nothing is read here. Which positions the input has and what can stand at each of them is
     * {@link InputDomain}'s, asked once and read by every measure; what this adds is which of them
     * an axis is drawn at, what each class is called and how a row for it is written.
     *
     * @param behavior what the axes are named after, which is the behavior the reading was made for
     */
    public static Partitioning of(String behavior, InputDomain inputs,
                                  souther.compiler.inputs.Quantities quantities, Symbols symbols,
                                  ReadingPolicy policy) {
        List<Axis> found = new ArrayList<>();
        java.util.Set<NumericTerm> uncertain = new java.util.LinkedHashSet<>();
        List<UnreadRule> unread = new ArrayList<>();
        // What the reading could not hold together, asked of every position it read rather than of
        // the ones left pending. This qualifies the classes and does not stand in for them: a
        // position with classes read from a product wider than the rules admit is exactly where it
        // has something to say, and a position with none is no more affected than any other.
        List<souther.compiler.inputs.PositionValuesNotSeparated> notSeparated = new ArrayList<>();
        for (Position position : inputs.positions()) {
            // Not at a position made of positions. Such a one is given up in favour of what is
            // under it and carries no classes of its own, so what this qualifies is not there —
            // and the same reading is said at each of the positions that do carry them, which is
            // where an author can act on it.
            if (position.valuesNotSeparated()
                    && !(position.structure()
                            instanceof souther.compiler.inputs.StructuralInspection.Decomposed)) {
                notSeparated.add(
                        new souther.compiler.inputs.PositionValuesNotSeparated(position.path()));
            }
            axisOf(behavior, position, symbols, policy, found, uncertain, unread);
        }
        // Every position the reading found, including the ones nothing divides: a report names what
        // it could not measure at one of those, and a body's comparison can still draw the first
        // line there. Nothing is dropped for how many there are. What an axis is worth is not known
        // here — `withThresholds` has not run, so a position a `guard` divides has no cut yet — and
        // a selection made now would be made where the least is known about what it selects
        // (see this package's documentation).
        List<Axis> kept = new ArrayList<>(found);
        // A position undivided because a rule about it went unread says that here, without waiting
        // for a body: a type bounded by a rule this cannot read is one whether or not any behavior
        // compares it. Nothing has compared anything yet, so what the rules came to is whether one
        // of them was left unread — settled beside each axis, as it is once a body has spoken.
        List<Measured> measured = new ArrayList<>();
        for (Axis axis : kept) {
            keep(new ArrayList<>(), measured, axis, null, unread);
        }
        MeasureClosure.Both closed = MeasureClosure.of(kept, List.of(), unread);
        return new Partitioning(kept, uncertain, undividedIn(measured),
                List.copyOf(unread), blockedIn(measured), List.copyOf(notSeparated),
                List.of(), List.of(), ReachingCuts.NONE, closed.partition(), closed.border());
    }

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
        // Whether this phase left anything at the position unread, and not which limit it was.
        // A limit belongs to the rule it stopped, and the findings carry it there; taken as the
        // position's, the first rule of however many were stopped alike was the one a report named.
        boolean anyUnread = rules.stream().anyMatch(one -> one.at().equals(axis.path()));
        measured.add(new Measured(axis, anyUnread ? new BodyCutInspection.Blocked()
                : new BodyCutInspection.Exhausted()));
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
     * The positions this reading did not get to the rules of, resolved.
     *
     * <p>Off the same pairing the verdict is, and neither is read from the other. Both phases have
     * spoken by the time a {@link Measured} exists — what the position's own declarations answered
     * and what a body's rules drew — and a candidate that neither of them answered is what an
     * author is waiting on. Written where the producer records it, every position holding an
     * `+Option+` said so whether or not the reading of it came to anything, and `not read` would be
     * a list of what this compiler cannot generally do rather than of what it did not read here.
     */
    private static List<souther.compiler.inputs.PositionReadingBlocked> blockedIn(
            List<Measured> measured) {
        List<souther.compiler.inputs.PositionReadingBlocked> out = new ArrayList<>();
        for (Measured each : measured) {
            PendingPosition pending = PendingPosition.of(each.axis());
            souther.compiler.inputs.PositionReadingBlocked stopped =
                    pending == null ? null : pending.reportable();
            if (stopped != null && !out.contains(stopped)) {
                out.add(stopped);
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
    public static Partitioning withThresholds(Partitioning base,
                                              souther.compiler.inputs.Quantities reading,
                                              List<Threshold> thresholds,
                                              Symbols symbols, ReadingPolicy policy) {
        return withThresholds(base, reading, thresholds, symbols, policy, List.of());
    }

    /**
     * The same, told which positions a comparison names that nothing turned into a line.
     *
     * <p>A position left undivided is not thereby a position the model divides no way. What this
     * takes in is the other half of that: the body compared it, and the form the comparison is
     * written in is one no reader here takes apart. Carried rather than re-derived, because the only
     * place that knows is the reader that gave up.
     */
    public static Partitioning withThresholds(Partitioning base,
                                              souther.compiler.inputs.Quantities reading,
                                              List<Threshold> thresholds,
                                              Symbols symbols, ReadingPolicy policy,
                                              List<UnreadRule> unread) {
        return withThresholds(base, reading, thresholds, symbols, policy, unread, List.of());
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
    public static Partitioning withThresholds(Partitioning base,
                                              souther.compiler.inputs.Quantities reading,
                                              List<Threshold> thresholds,
                                              Symbols symbols, ReadingPolicy policy,
                                              List<UnreadRule> unread,
                                              List<GuardThresholds.Guards.Singled> singled) {
        return withThresholds(base, reading, thresholds, symbols, policy, unread, singled, List.of());
    }

    /**
     * The same, with the lines a body draws between two of its positions.
     *
     * <p>Carried through rather than derived here. A line between two positions divides neither of
     * them, so nothing about it belongs to an axis — it is read where the comparison is and travels
     * beside the partition, which is what keeps a position the classes could say nothing about from
     * losing the line its body draws about it.
     */
    public static Partitioning withThresholds(Partitioning base,
                                              souther.compiler.inputs.Quantities reading,
                                              List<Threshold> thresholds,
                                              Symbols symbols, ReadingPolicy policy,
                                              List<UnreadRule> unread,
                                              List<GuardThresholds.Guards.Singled> singled,
                                              List<LineDrawn> between) {
        return withThresholds(base, reading, thresholds, symbols, policy, unread, singled, between,
                souther.compiler.check.PathReachability.Answers.NONE, List.of());
    }

    /**
     * The same, told what arrives at each comparison.
     *
     * <p>A comparison one of whose outcomes nothing takes draws no line. It is written, it is read,
     * and what it divides is nothing that gets there — {@code guard a.value < 6000} under
     * {@code guard a.value < 5000} puts a line at six thousand through values that are all under
     * five, and a report asking for a row either side of it is asking for a row nobody can write.
     *
     * <p>Asked of the reading of the whole body, not of the position's own values. Whether a line
     * falls inside what the position can hold is the other question and is asked below: that one is
     * what the classes are built out of, and a cut outside the interval it divides is not a partition
     * of anything. Both are needed and neither is the other — a line well inside a position's values
     * can still be one nothing on the way to it can be either side of.
     */
    public static Partitioning withThresholds(Partitioning base,
                                              souther.compiler.inputs.Quantities reading,
                                              List<Threshold> thresholds,
                                              Symbols symbols, ReadingPolicy policy,
                                              List<UnreadRule> unread,
                                              List<GuardThresholds.Guards.Singled> singled,
                                              List<LineDrawn> between,
                                              souther.compiler.check.PathReachability.Answers
                                                      arrives,
                                              List<GuardThresholds.Guards.AtAPosition> compared) {
        return withThresholds(base, reading, thresholds, symbols, policy, unread, singled, between, arrives,
                compared, ReachingCuts.NONE);
    }

    /**
     * The same, told what a row has already had to satisfy by the time it reaches each comparison.
     *
     * <p>Carried and not re-derived, which is the whole discipline {@link ReachingCuts} is written
     * around: what a region may assume is what the walk of the body actually took in, and a reading
     * that recovered it from where a comparison sits would be free to name a condition nothing here
     * could read.
     */
    public static Partitioning withThresholds(Partitioning base,
                                              souther.compiler.inputs.Quantities reading,
                                              List<Threshold> thresholds,
                                              Symbols symbols, ReadingPolicy policy,
                                              List<UnreadRule> unread,
                                              List<GuardThresholds.Guards.Singled> singled,
                                              List<LineDrawn> between,
                                              souther.compiler.check.PathReachability.Answers
                                                      arrives,
                                              List<GuardThresholds.Guards.AtAPosition> compared,
                                              ReachingCuts reaching) {
        // Both producers of one kind of evidence. What a body compared and what a type's own rules
        // bound are read by different readers and answer the same question, so a position either of
        // them wrote about and neither could turn into a line is named once, whichever wrote it.
        List<UnreadRule> rules = new ArrayList<>(base.unread());
        for (UnreadRule each : unread) {
            if (rules.stream().noneMatch(had -> had.sameAs(each))) {
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
                NumericDomain.Bounds only = domainOf(reading, term);
                NumericTerm at = term;
                Axis here2 = axis;
                keep(out, measured, refine(axis,
                        () -> singledClasses(points, at, here2.type(), only, symbols),
                        mergedPoints(axis.cuts(), points, at.carrierAt(axis.type(), symbols)),
                        axis.parted()),
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
            NumericDomain.Bounds domain = domainOf(reading, term);
            // Filtered once, and both answers read the filtered list. A line outside what the
            // position holds divides nothing, and it is not a boundary either: leaving it in the
            // cuts while the intervals dropped it asks for a row at a value the record refuses,
            // which is the thing being fixed here happening again one field over. The end the
            // position stops short of is outside it as much as anything past it is.
            List<Threshold> reachable = here.stream()
                    // Asked of the place the line falls at, which the position need not hold a
                    // value at. Read off the value, a line between two of the position's values was
                    // dropped as one the rules leave nothing at.
                    .filter(t -> domain == null || admits(domain, t.parts()))
                    // And what the guards above it left. Only a proof drops a line: a comparison
                    // this could not settle keeps its line and its rows, which is the direction that
                    // leaves an author with work rather than with a report about a model of theirs
                    // that is fine.
                    // Asked of the comparison, where the rule is met by having produced one. A
                    // clause has no comparison a path can arrive at: it is checked whenever the
                    // behavior answers, so nothing about which branch a body took drops its line.
                    .filter(t -> t.origin().comparisonAt().stream()
                            .noneMatch(arrives::dividesNothing))
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
                                    within == null ? null : within.max(), carrier),
                            measuredAt, read.type(), policy, symbols,
                            within == null ? null : within.min(),
                            within == null ? null : within.max()),
                    merged(axis.cuts(), reachable, carrier),
                    reachable.stream().map(Threshold::parts).toList()),
                    reachable.isEmpty() ? null : new BodyCutInspection.Evidence(), rules);
        }
        MeasureClosure.Both closed = MeasureClosure.of(out, compared, rules);
        return new Partitioning(out, base.uncertain(),
                undividedIn(measured), List.copyOf(rules), blockedIn(measured),
                // Carried across: what a reading could not hold together is a fact about the
                // declarations, and a body drawing a line on a position does not make the product
                // it was read from the relation the rules admit.
                // Turned into borders here and nowhere else, so that every rule about one
                // quantity is arranged together however the rules were written — a body's
                // condition and a clause cut one form as readily as two conditions do.
                // Every rule about one quantity arranged together, whichever producer its border
                // came from. A line that divides a position leaves its division on the axis and,
                // where the position has no value beside it, its border over here — and the two
                // sides of that border are runs of what all of them leave.
                base.notSeparated(), Border.allOf(between, partedByQuantity(out)), compared,
                reaching, closed.partition(), closed.border());
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
                               List<Cut> cuts, List<Seam> parted) {
        return axis.carrying(axis.derivable() ? axis.classes() : otherwise.get(), cuts, parted);
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
                    holding(term, carrier, new Recognition.CountIs.At(value)),
                    standing(type, carrier, value, symbols)));
        }
        Place other = carrier.somethingOtherThan(values, within);
        String label = "/= " + String.join(", ",
                values.stream().map(carrier::written).toList());
        Recognition away = holding(term, carrier,
                new Recognition.CountIs.AwayFrom(values));
        classes.add(other == null
                ? PartitionClass.ungeneratable(term + "/" + label, label, away,
                        "nothing here composed a value of this position other than the ones"
                                + " singled out")
                : classAt(term + "/" + label, label, away,
                        standing(type, carrier, other, symbols)));
        return List.copyOf(classes);
    }

    /** A class over the one value that stands for it, or one nothing produces where there is no
     *  such value — which is what a position wearing a name this module cannot write leaves. */
    private static PartitionClass classAt(String id, String label, Recognition is,
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

    /** A class that reads the term's count out of a row and answers about it. */
    private static Recognition holding(NumericTerm term, Carrier carrier,
                                          Recognition.CountIs is) {
        return new Recognition.OfACount(term, carrier, is);
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

    /**
     * What the rules leave one term, including a term an axis only took on here.
     *
     * <p>Which numbers a position is measured at is not settled by the reading of the declarations
     * alone: a bare list nothing bounds becomes an axis about its length where a body measures it,
     * and what such a term guarantees of its own values is what bounds it. Asked of the reading
     * rather than kept per term beside it, which is where the two came to disagree.
     */
    private static NumericDomain.Bounds domainOf(souther.compiler.inputs.Quantities reading,
                                                 NumericTerm term) {
        return reading.runsBetween(term);
    }

    /**
     * Where the rules part each of this behavior's quantities, by the quantity they are on.
     *
     * <p>Read off the axes, which is where a division of a position is recorded whether or not the
     * position has a value at it. A line over a form of several positions divides none of them and
     * is on a quantity of its own, which no axis names — those arrive with the lines themselves.
     */
    private static Map<String, List<Seam>> partedByQuantity(List<Axis> axes) {
        Map<String, List<Seam>> out = new LinkedHashMap<>();
        for (Axis axis : axes) {
            if (axis.parted().isEmpty()) {
                continue;
            }
            out.computeIfAbsent(QuantityKey.of(NumericDomain.LinearForm.atom(axis.term())).key(),
                    _ -> new ArrayList<>()).addAll(axis.parted());
        }
        return out;
    }

    /** Whether the rules leave the quantity anything at the place a line falls. */
    private static boolean admits(NumericDomain.Bounds within, Seam parts) {
        return (within.min() == null || parts.at().compare(within.min().at()) <= 0)
                && (within.max() == null || parts.at().compare(within.max().at()) >= 0);
    }

    private static List<Cut> merged(List<Cut> had, List<Threshold> thresholds, Carrier carrier) {
        Map<String, Cut> byValue = new LinkedHashMap<>();
        for (Cut cut : had) {
            byValue.put(cut.key(), cut);
        }
        for (Threshold each : thresholds) {
            // A line the position has no value at is not a cut of it. It divides the position all
            // the same — the classes either side are what the model distinguishes — and there is no
            // value for a row to be written at, so there is no border here either. The rule's own
            // border is on the quantity it wrote, which can name the line.
            if (each.value() == null) {
                continue;
            }
            Cut cut = Cut.at(carrier, each.value(), each.origin());
            byValue.merge(cut.key(), cut, (there, _) -> there.and(each.origin()));
        }
        return List.copyOf(byValue.values());
    }

    /**
     * The borders a position's rules drew, one per rule that drew a cut.
     *
     * <p>One entry per line and not per point. What each of them owes a row at, in each of the four
     * roles the technique names, is the border's own answer — including the roles it owes nothing in
     * and why. Built as a list of points instead, a role nobody was owed a row in and a role this
     * reader forgot to build were the same thing.
     *
     * <p>Keeping a rule per cut means the same value can be owed three times. That is the point: an
     * invariant and two guards that name one value are three rules, and a row that meets one of them
     * has met one.
     */
    public static List<Border> bordersOf(Axis axis, Symbols symbols,
                                         NumericDomain.Bounds within) {
        List<Border> out = new ArrayList<>();
        // Every place the rules part this position's values, collected before any border is built.
        // What each border owes away from its line is a run of the arrangement they make together,
        // and a border built without them reads its two sides to the end of the order — so a row in
        // the partition after next answered for a point inside the one this border bounds.
        // Every place the rules part this position's values: the ones its cuts stand at, and the
        // ones no cut stands at because the position holds no value there. A border built from the
        // cuts alone read its two sides past exactly the lines that were left out.
        List<Seam> parted = new ArrayList<>(axis.parted());
        for (Cut cut : axis.cuts()) {
            BoundaryTarget where = BoundaryTarget.at(
                    new BorderQuantity.OfACoordinate(axis.id(), axis.term(), cut.carrier()),
                    new Level.OnACarrier(cut.carrier(), cut.at()));
            for (OriginRef origin : cut.origins()) {
                Seam parts = Border.parts(where, origin);
                if (parts != null && parted.stream()
                        .noneMatch(had -> had.key().equals(parts.key()))) {
                    parted.add(parts);
                }
            }
        }
        for (Cut cut : axis.cuts()) {
            // The carrier is the cut's, which is the one the rule was read on. Asked of the axis
            // instead, a line drawn on a count taken of a position would be written back as a value
            // of the position.
            BoundaryTarget target = BoundaryTarget.at(
                    new BorderQuantity.OfACoordinate(axis.id(), axis.term(), cut.carrier()),
                    new Level.OnACarrier(cut.carrier(), cut.at()));
            for (OriginRef origin : cut.origins()) {
                // Null where the position does not reach the line at all, which is the line and not
                // one of its points: the rule drew it about the type, and what is left of the type
                // here may stop short of it — `low < high` under one `[0, 1]` leaves `low` every
                // value up to 1 and not 1 itself.
                Border border = Border.at(target, origin, within, parted);
                if (border != null) {
                    out.add(border);
                }
            }
        }
        return List.copyOf(out);
    }

    /**
     * One position, turned into an axis or given up in favour of what is under it.
     *
     * <p>The local answer first, whole: the classes the position's declarations state and the lines
     * its rules draw come back as one value, so what "local evidence ran out" means is an answer
     * rather than two empty lists to be noticed. Only where it ran out does what the position is
     * made of decide anything — a position its own declarations answered for keeps its axis,
     * whatever is under it, and that precedence is the arm this is written in rather than the order
     * of two {@code if}s.
     *
     * <p>Of the structural answers only {@code Children} takes the position away: the fields are
     * positions of their own and were read as such, and the classes belong to them. A leaf and a
     * block both leave the position standing, pending what a body's rules say later.
     *
     * <p><b>A position with local evidence and children is unreachable today, and is refused rather
     * than resolved.</b> Only a product has children, and a product states no distinction — its type
     * declares no division — and carries no cut, having no order for a rule to name a value on. A
     * language that grew one would have this reader keeping the parent's axis while the reading kept
     * its fields, and two readers of one input disagreeing about which positions there are is the
     * thing this arrangement exists to stop.
     */
    private static void axisOf(String behavior, Position position, Symbols symbols,
                               ReadingPolicy policy,
                               List<Axis> out, java.util.Set<NumericTerm> uncertain,
                               List<UnreadRule> unread) {
        for (UnreadRule each : position.unreadRules()) {
            if (unread.stream().noneMatch(had -> had.sameAs(each))) {
                unread.add(each);
            }
        }
        NumericTerm term = position.term();
        AxisId id = AxisId.of(behavior, term);
        switch (LocalInspection.of(position, symbols, policy)) {
            case LocalPartition.Divided divided -> {
                if (position.structure() instanceof StructuralInspection.Decomposed) {
                    throw new IllegalStateException(
                            "`" + position.path() + "` both divides and is made of positions; the"
                                    + " reading of an input and the axes drawn from it disagree"
                                    + " about which positions there are");
                }
                if (divided.cuts() instanceof CutEvidence.Present drawn && drawn.uncertain()) {
                    uncertain.add(term);
                }
                out.add(new Axis(id, term, position.type(), divided.classes(),
                        divided.cuts().cuts(), List.of(), divided.unanswered(),
                        divided.rulesNotReached(), null, null));
            }
            // Nothing local divides the position, which is what licenses asking what it is made of.
            // Whether the reading got to the end of the rules is carried rather than acted on here:
            // a position made of positions is given up in favour of what is under it either way,
            // and a rule about the whole value that this could not read says nothing about which of
            // its fields it would have divided.
            case LocalPartition.Open _, LocalPartition.Blocked _ -> {
                switch (position.structure()) {
                    // The one answer that takes the position away: what is under it is what the
                    // classes belong to, and those positions were read on their own.
                    case StructuralInspection.Decomposed _ -> { }
                    // A leaf and a block are both positions still to be answered for, and each
                    // carries what it is left with if nothing answers — including a rule about this
                    // position that the local reading could not take in, which is what keeps the
                    // position from completing as one the model divides no way.
                    case StructuralInspection.Retained retained ->
                            out.add(Axis.pendingAt(id, term, position.type(),
                                    position.unansweredQuestions(), position.rulesNotReached(),
                                    retained.continuation(), leftUnread(position)));
                }
            }
        }
    }




    /**
     * What a position with no evidence is left with, where an absence may not be concluded from it.
     *
     * <p>The end reading's answer ahead of the value reading's, where both have one. A rule this
     * read for a line and could not use is the nearer of the two: lifting that limit is what would
     * give the position an axis, and the reading that turns clauses into sets of values has no word
     * for a range at all — so it names one limit while the report's own line names another, and one
     * position came back with two causes for one clause.
     *
     * <p>The first, as a comparison's is. What a reader has to lift is the first limit in the way.
     */
    private static BlockReason leftUnread(Position position) {
        return position.unreadRules().isEmpty() ? position.valuesUnread()
                : position.unreadRules().getFirst().why();
    }

    // --- small helpers ----------------------------------------------------------------------------

    /** Values that could stand for a type wherever nothing else has been said about the position — the
     * inner value of a newtype, a field no axis divides. A record is not one of these: its fields are
     * composed, which is the generator's work and not a value this can hand over. */
    static List<FixtureTemplate> representativesOf(Type type, Symbols symbols,
                                                   ReadingPolicy policy) {
        return representativesOf(type, symbols, policy, null);
    }

    /**
     * The same, for a position the record it sits in has already narrowed.
     *
     * <p>{@code within} is what is left of the position once the rest of the assignment is settled:
     * an {@code endsAt} beside a {@code startsAt} of 1439 can only be 1440, and the value this offers
     * has to come from there rather than from the bottom of the type's own range.
     */
    static List<FixtureTemplate> representativesOf(Type type, Symbols symbols, ReadingPolicy policy,
                                                   NumericDomain.Bounds within) {
        return representativesOf(type, symbols, policy, within, java.util.Set.of());
    }

    /**
     * The same, with the newtypes this is already inside the value of.
     *
     * <p>Carried because what stands for a collection is built from what stands for its element, which
     * is this question again. A name met while its own value is being built is a type written in terms
     * of itself and is given up on — the names and not a count of them, since how many names a value
     * wears on the way down is not what has to be stopped.
     */
    static List<FixtureTemplate> representativesOf(Type type, Symbols symbols, ReadingPolicy policy,
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
        List<PartitionClass> classes = PartitionClasses.of(type, symbols, policy);
        for (PartitionClass each : classes) {
            List<FixtureTemplate> stands = standingFor(each.representatives(), symbols, policy, expanding);
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
        // A unit data is one value, and naming it writes it. Read through the classes above it has
        // none — nothing tells its one value from another — so what stands for it is said here, in
        // the same words a class of a sum says it in. Left out, a position holding one was a
        // position nothing could write a value at, which is what a case of a sum narrows to.
        if (type instanceof Type.Ref unit
                && symbols.declarations().declaration(unit.name().key()) instanceof Hir.UnitData) {
            return symbols.scope().reach(unit.name()) instanceof TypeReachName.Written written
                    ? List.of(FixtureTemplate.unitCase(written)) : List.of();
        }
        // A newtype the model only bounds has no classes — everything outside the bound is refused at
        // construction — but it does have values, and the edge of the bound is one that builds.
        if (type instanceof Type.Ref ref && symbols.declarations().declaration(ref.name().key()) instanceof Hir.Data data) {
            if (!data.newtype()) {
                return composed(ref.name(), symbols, policy, expanding);
            }
            // A newtype nothing here names has no value anything here can write: the name goes on
            // the value as it is written, and there is none to put on.
            return symbols.scope().reach(ref.name()) instanceof TypeReachName.Written written
                    ? insideTheNewtype(ref.name(), symbols, policy, within, expanding).stream()
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
                                             ReadingPolicy policy,
                                             java.util.Set<TypeSymbol> expanding) {
        return switch (source.evaluate()) {
            case RepresentativeSource.Evaluation.Values values -> values.written();
            case RepresentativeSource.Evaluation.Compose compose ->
                    composed(compose.through(), symbols, policy, expanding).stream()
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
                                                  ReadingPolicy policy,
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
        FieldDomains left = FieldDomains.of(record, data, symbols, policy, settled);
        Map<String, FixtureTemplate> chosen = new LinkedHashMap<>();
        for (Map.Entry<String, Type> field : fields.entrySet()) {
            List<FixtureTemplate> stands = representativesHolding(field.getValue(), symbols,
                    policy, left.at(field.getKey()), left.heldAt(field.getKey()), inside);
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
                left = FieldDomains.of(record, data, symbols, policy, settled);
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

    /** How many the rules on a value of {@code type} allow it to hold, where the record the position
     *  sits in has a rule about it too: {@link DeclaredBounds#mostCountOf}. */
    static int mostHeld(Type type, Symbols symbols, FieldDomains.Held held) {
        return DeclaredBounds.mostCountOf(type, symbols, held);
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
                                                           ReadingPolicy policy,
                                                            FieldDomains.Held held) {
        return Witnesses.heldBackFor(TypeOps.base(type, symbols), leastHeld(type, symbols, held),
                symbols, policy);
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
                                                        ReadingPolicy policy,
                                                        NumericDomain.Bounds within,
                                                        FieldDomains.Held held) {
        return representativesHolding(type, symbols, policy, within, held, java.util.Set.of());
    }

    /** The same, with the names this is already inside the value of, for the same reason
     *  {@link #representativesOf} carries them. */
    static List<FixtureTemplate> representativesHolding(Type type, Symbols symbols,
                                                        ReadingPolicy policy,
                                                        NumericDomain.Bounds within,
                                                        FieldDomains.Held held,
                                                        java.util.Set<TypeSymbol> expanding) {
        List<FixtureTemplate> candidates = new ArrayList<>();
        // Under every name the position wears, because a floor read off the record says how much the
        // value holds and not what it is written as: a field of a newtype over a list takes a list
        // inside that newtype's own name.
        for (FixtureTemplate bare : Witnesses.holding(TypeOps.base(type, symbols),
                leastHeld(type, symbols, held), symbols, policy, expanding)) {
            candidates.add(Witnesses.wrapped(type, bare, symbols));
        }
        candidates.addAll(representativesOf(type, symbols, policy, within, expanding));
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
                                                            ReadingPolicy policy,
                                                            NumericDomain.Bounds within,
                                                            FieldDomains.Held held) {
        List<FixtureTemplate> base =
                new ArrayList<>(representativesHolding(type, symbols, policy, within, held));
        // What a position holds back for the product search's second pass is on offer here from the
        // start. This pass runs only where both of those have already failed, and a position keeping
        // a value from the last search there is a value nothing will ever be tried at.
        for (FixtureTemplate kept : inReserve(type, symbols, policy, within)) {
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
    static List<FixtureTemplate> insideTheNewtype(TypeSymbol newtype, Symbols symbols,
                                                  ReadingPolicy policy) {
        return insideTheNewtype(newtype, symbols, policy, null, java.util.Set.of());
    }

    static List<FixtureTemplate> insideTheNewtype(TypeSymbol newtype, Symbols symbols,
                                                          ReadingPolicy policy,
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
        Place held = bounds == null || bounds.saysNothing() ? null : inside(bounds, own.carrier());
        FixtureTemplate at = held == null ? null
                : FixtureTemplate.on(own.carrier(), held, symbols.scope()::reach);
        if (at != null) {
            candidates.add(at);
        }
        if (base == Type.STRING && symbols.declarations().declaration(newtype.key()) instanceof Hir.Data data) {
            for (Hir.InvariantClause clause : TypeOps.effectiveInvariants(data, symbols)) {
                for (Hir.Expr each : ClauseHelpers.conjunctsOf(clause.expr())) {
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
                symbols, policy, inside));
        candidates.addAll(representativesOf(base, symbols, policy, null, inside));

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
    static List<FixtureTemplate> inReserve(Type type, Symbols symbols, ReadingPolicy policy,
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
        return representativesOf(type, symbols, policy, within).stream()
                .map(FixtureTemplate::text).anyMatch(held.text()::equals)
                ? List.of() : List.of(held);
    }

    private Partitions() {}
}
