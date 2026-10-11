package souther.compiler.inputs;

import souther.compiler.check.DateShifts;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.ElementAnswer;
import souther.compiler.check.NumericMeasures;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.SeededWalk;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.check.WalkElements;
import souther.compiler.core.Core;
import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.ValueTransformation;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/**
 * Which number of a behavior's input an expression names, or nothing where it names none.
 *
 * <p>The companion of {@link InputPath}, one question further in. That answers which location an
 * expression points at; this answers which number a rule about it is written on, which is the
 * location's own content or something taken of it — and the two are not the same answer, because a
 * position holding a string is a position holding no number while every rule about its length is
 * about one.
 *
 * <p>One answer, for every reader that has to say which number a comparison is about. The reading
 * that draws lines and the reading that names what a run was steered by both ask it, and each
 * working it out for itself is two accounts of one number: matched afterwards by how a path is
 * spelled, two numbers taken of one location are one, which is the whole of what a line drawn on
 * the second of them is lost to.
 *
 * <p>Which of the standard library's calls take a number of a location is asked of
 * {@link NumericMeasures} rather than decided here, and asked of the operation the call resolved to
 * rather than of its spelling.
 */
public final class InputNumber {

    private InputNumber() {
    }

    /**
     * The number {@code e} names.
     *
     * <p>The argument of a taking has to be a location: {@code List.length(List.map(f, xs))} counts
     * something no path names, and a boundary on it could not be looked for in a row.
     */
    public static NumericTerm of(Core e, InputDomain inputs, InputReads reads,
                                 RuleReadingSource source) {
        Symbols symbols = source.symbols();
        NumericMeasures.Measured measured = NumericMeasures.takenIn(e, symbols);
        if (measured != null) {
            // A taking is of a location, or of what a location's value was moved into, so an
            // argument that is neither is one there is no location to take it of.
            ObservationSource of = sourceOf(measured.of(), reads, source);
            if (of != null) {
                return NumericTerm.TakenOf.of(measured.operation(), of, measured.arguments(),
                        inputs.typeAt(of.position(), source), source.inners(), symbols);
            }
            // A location the operation is not taken of, or a value standing at none. The second is
            // a walk's answer, and a number over the values it walked is a term of its own where
            // those values are read from a place.
            return overARun(measured, inputs, reads, source);
        }
        // And a number of the input is the value at a position, so an expression naming none names
        // no number here.
        return switch (reads.pathOf(e, source.newtypes())) {
            case PathResolution.At(var at) -> new NumericTerm.ValueOf(at);
            case PathResolution.NotAPosition _ -> null;
            // And a number of the input is the value at one position. A name standing at one of
            // several would be a number at whichever of them a reader picked, and a line drawn on
            // it would fall at a place the rule may say nothing about.
            case PathResolution.MayStandAt _ -> null;
        };
    }

    /**
     * The value a taking is of: the one standing at a location, or one a chain of shifts of a date
     * written out made of it. Null where it is neither.
     *
     * <p>A location is asked first and is what a taking is of wherever it is one. A call that is no
     * location is then asked what the library says of it ({@link DateShifts}), so that a date moved
     * by days is a value of the place it was moved from and not a place of its own: a name that
     * only may stand at a location is still no one of them.
     */
    private static ObservationSource sourceOf(Core of, InputReads reads,
                                              RuleReadingSource source) {
        return switch (reads.pathOf(of, source.newtypes())) {
            case PathResolution.At(var at) -> ObservationSource.asItStands(at);
            case PathResolution.NotAPosition _ -> movedFromALocation(of, reads, source);
            // A taking is of one location, and a name that only may stand at one is no one of
            // them. Taken of any, the number would be a size of a container the run it is on
            // never walked.
            case PathResolution.MayStandAt _ -> null;
        };
    }

    /**
     * The location a chain of shifts of a date starts from and what the chain comes to, or null
     * where {@code of} is no shift of a date or what it shifts is no location.
     *
     * <p>Each step is read where the date inside it stands, since a name given a shifted date is
     * the shift and the binding is where its date is read.
     */
    private static ObservationSource movedFromALocation(Core of, InputReads reads,
                                                        RuleReadingSource source) {
        // A shift of a date answers a date, so anything else is no chain and the walk below, which
        // resolves names, is not spent on it.
        if (!Type.DATE.equals(Core.withoutStanding(of).type())) {
            return null;
        }
        Symbols symbols = source.symbols();
        List<Long> days = new ArrayList<>();
        Denotation met = reads.denotes(of, symbols, source.newtypes());
        for (DateShifts.Step step = DateShifts.stepOf(met.value(), symbols); step != null;
                step = DateShifts.stepOf(met.value(), symbols)) {
            days.add(step.days());
            met = met.at().denotes(step.date(), symbols, source.newtypes());
        }
        if (days.isEmpty()
                || !(met.at().pathOf(met.value(), source.newtypes())
                        instanceof PathResolution.At(var from))) {
            return null;
        }
        // The innermost shift first: each one is defined only at the dates the ones inside it
        // leave, which is what the translation keeps and the days alone would not.
        DateTranslation translation = DateTranslation.none();
        for (Long each : days.reversed()) {
            translation = translation.thenAddDays(each);
            if (translation == null) {
                return null;
            }
        }
        return new ObservationSource(from, ValueTransformation.of(translation));
    }

    /**
     * The number {@code measured} takes over the values a walk was given, or null where those
     * values are not read from a place.
     *
     * <p>Three answers have to be in hand, and each is somebody else's. That the walk answers one
     * value per element of what it was given is a fact about the operation that handed the closure
     * its elements, proved before the tree was rewritten. Where in an element the answer stands is
     * what the closure came to, read once and kept as the way there. And which position the
     * elements are at is the reading of the input's, as it is for every other term.
     *
     * <p>What the walk itself supplies is the element's binding and nothing more. The form it has
     * now is what a rewrite left, so it is asked for an identity and not for a meaning: reading the
     * answer off the shape would make the walks a rule can be written over a consequence of which
     * ones that rewrite happens to recognise, and a walk an author wrote by hand would be read as
     * a {@code map}.
     *
     * <p>The walk is met under whatever name is in scope, and what a name stands for is asked of
     * the reading that owns the question ({@link InputReads#meaningOf}) rather than read off the
     * tree. A model of any size binds the mapped list before totalling it, and a route that walked
     * only the expression as written would answer one thing for
     * {@code List.sum(List.map(f, xs))} and another for the same rule with a name in the middle —
     * which is a `let` changing what a model means. The environment the value was given in comes
     * with it, so what is read of the walk afterwards is read where the walk stands.
     *
     * <p>Where the answer is no place of the element but something made of its fields, the run is
     * over what was computed of each element instead ({@link #overWhatWasComputed}), and is the run
     * over a place where what was computed is that place.
     *
     * <p>Null wherever any of the three is missing, which is a rule this compiler did not read
     * rather than a rule the model does not state — and is reported as one. Null too where the three
     * are in hand and what they come to is not one run
     * ({@link RunSource#overTheOccurrencesAt}), which is the same answer for the same reason: a
     * reading short rather than a line somewhere it does not go.
     */
    private static NumericTerm overARun(NumericMeasures.Measured measured, InputDomain inputs,
                                        InputReads reads, RuleReadingSource source) {
        Symbols symbols = source.symbols();
        // A number over a run is named by the operation and where the values are read from, and a
        // taking given a value beside them is a number those two do not name. Read without it, the
        // total of one part of each element would be the total of another.
        if (!measured.arguments().none()) {
            return null;
        }
        // The walk and the names it stands under, which travel together: a name bound inside a
        // helper stands for what the call handed over, and what is read of that afterwards is read
        // where it stands rather than where the name was.
        Denotation met = reads.denotes(measured.of(), symbols, source.newtypes());
        Core walk = met.value();
        InputReads where = met.at();
        BindingId element =
                WalkElements.elementBindingOf(walk, where, symbols, source.newtypes());
        if (element == null) {
            return null;
        }
        ElementProjection answered = where.projectionAt(element);
        // Where the elements stand, and nothing where they stand nowhere: a run is over the values
        // at a position, so a container this reading could not place leaves no run to take.
        TermPath at = switch (where.elementAt(element, source.newtypes())) {
            case PathResolution.At(var stands) -> stands;
            case PathResolution.NotAPosition _ -> null;
            // A run is over the values at one position, and a walk whose elements come from more
            // than one container is no one run.
            case PathResolution.MayStandAt _ -> null;
        };
        if (at == null) {
            return null;
        }
        ElementValue computed = null;
        if (answered == null) {
            computed = computedOf(measured, where, element, source);
            if (computed == null) {
                return null;
            }
            // What was computed may be the element's own field and nothing made of it, as a closure
            // that weighs a field once and adds nothing is. That is the place, and one number has
            // one term whichever way its closure was spelled.
            answered = placeStanding(computed, where.answerAt(element), at, inputs, source);
        }
        if (answered == null) {
            return overWhatWasComputed(measured, where.answerAt(element), computed, at, source);
        }
        TermPath under = answered.from(at);
        // Whether what is read from there is one run is the run's own question, and it is asked
        // rather than assumed: a walk over a container inside another container is over some of the
        // occurrences of its path, and a term made of it would state of every one of them what the
        // model says of those.
        RunSource over = RunSource.overTheOccurrencesAt(under);
        // A walk inside a container of containers is over some of the occurrences of its path,
        // unless what it walked is every one of them: the lists of an outer list put end to end.
        if (over == null && where.everyElementAt(element, source.newtypes())
                instanceof PathResolution.At(TermPath every) && every.equals(at)) {
            over = RunSource.overEveryOccurrenceAt(under);
        }
        if (over == null) {
            return null;
        }
        Type stands = inputs.typeAt(under, source);
        return stands == null ? null
                : NumericTerm.TakenOver.of(measured.operation(), over, stands, source.inners(),
                        symbols);
    }

    /**
     * What a walk from a seed answers where its step only adds to the answer so far: the seed and
     * the total of what the step adds for each element.
     *
     * @param seed  what the walk starts from
     * @param total the total of what each element adds, the term {@code List.sum} of the same
     *              values is
     */
    public record SeedAndTotal(ExactRatio seed, NumericTerm total) {}

    /**
     * What {@code e} is, where it is a walk from a seed ({@link SeededWalk}) whose step answers the
     * answer so far and something of the element alone: the seed, and the total of those somethings
     * over the elements at one position. Null where it is any other walk, or where the elements are
     * not read from a place.
     *
     * <p>By induction over the walk the answer is {@code seed + Σ w(x)}, where {@code w(x)} is what
     * the step answers for an accumulator of nought. The step adds exactly that and nothing else
     * where it moves by one for each unit of the accumulator and by the same everywhere else, which
     * is asked of two readings of the step rather than of its spelling: the step read at an
     * accumulator of nought and at one of one differ by the accumulator and by nothing the element
     * holds. {@code acc + x}, {@code x + acc} and {@code Decimal.add(acc, x)} are one step.
     *
     * <p>The total is the term {@code List.sum} of those values is, so a rule over a fold and a rule
     * over a sum of the same numbers are about one number.
     *
     * @param blockOf the block a closure argument stands for, where the call stands
     */
    public static SeedAndTotal ofAWalkAdding(Core e, InputDomain inputs, InputReads reads,
                                             RuleReadingSource source,
                                             Function<Core, Core.Block> blockOf) {
        SeededWalk walk = SeededWalk.of(e, blockOf);
        if (walk == null) {
            return null;
        }
        Denotation container =
                reads.standing(walk.container(), source.symbols(), source.newtypes());
        // Every occurrence of the position and each as often, which a total of what each element
        // adds is a total of.
        if (!(container.at().everyElementOf(container.value(), source.newtypes())
                instanceof PathResolution.At(TermPath at))) {
            return null;
        }
        BindingId element = walk.element().binding();
        ElementAnswer step = new ElementAnswer(element, walk.step().body());
        int accumulatorAt = walk.step().params().indexOf(walk.accumulator());
        Type counted = accumulatorAt < 0 ? null : walk.step().paramTypes().get(accumulatorAt);
        // The body's names are copied once, and the accumulator put at each of the two figures in
        // turn: a reading keeps nothing of the names it was given.
        Map<BindingId, Core> held = new HashMap<>(reads.heldByTheBody());
        if (!holds(held, walk.accumulator().binding(), counted, 0)) {
            return null;
        }
        ElementValue.Affine nought = affine(ElementValue.read(step, held, source));
        if (nought == null || nought.form().coefs().isEmpty()) {
            return null;
        }
        holds(held, walk.accumulator().binding(), counted, 1);
        ElementValue.Affine one = affine(ElementValue.read(step, held, source));
        ElementValue.Affine seed = affine(ElementValue.read(
                new ElementAnswer(element, walk.seed()), held, source));
        if (seed == null || one == null || !seed.form().coefs().isEmpty()
                || !nought.form().coefs().equals(one.form().coefs())
                || !(one.form().constant().minus(nought.form().constant())
                        instanceof ExactAnswer.Held<ExactRatio>(ExactRatio moved))
                || !ExactRatio.ONE.equals(moved)) {
            return null;
        }
        ElementProjection place = nought.asAPlace();
        NumericTerm total;
        if (place != null && TypeOps.base(walk.step().body().type(), source.inners()).equals(
                TypeOps.base(inputs.typeAt(place.from(at), source), source.inners()))) {
            RunSource over = RunSource.overEveryOccurrenceAt(place.from(at));
            total = over == null ? null
                    : NumericTerm.TakenOver.of(SUM, over, inputs.typeAt(place.from(at), source),
                            source.inners(), source.symbols());
        } else {
            Type each = walk.step().body().type();
            RunSource over = RunSource.computedOverTheElementsAt(at, nought, each);
            total = over == null ? null
                    : NumericTerm.TakenOver.of(SUM, over, each, source.inners(), source.symbols());
        }
        return total == null ? null : new SeedAndTotal(seed.form().constant(), total);
    }

    private static final ValueName.Stdlib.Operation SUM =
            ValueName.Stdlib.operation("List", "sum");

    private static ElementValue.Affine affine(ElementValue read) {
        return read instanceof ElementValue.Affine form ? form : null;
    }

    /** Puts the accumulator at {@code value} of the type it counts in, or says it counts in a type
     *  no literal is written for. */
    private static boolean holds(Map<BindingId, Core> held, BindingId accumulator, Type type,
                                 long value) {
        if (Type.INT.equals(type)) {
            held.put(accumulator, new Core.Int(value, type, null));
            return true;
        }
        if (Type.DECIMAL.equals(type)) {
            held.put(accumulator, new Core.Decimal(BigDecimal.valueOf(value), type, null));
            return true;
        }
        return false;
    }

    /**
     * The field {@code computed} is, where it is that field as the same kind of number, or null.
     *
     * <p>The same number is not the same term. What a total is counted as is part of it, and a call
     * that changes only that — whole numbers as decimals — computes the field's number and is not
     * the field: two lines of the largest whole number come to a decimal and to no whole number.
     * So a form that is a field is the place only where what the closure answers stands as what the
     * field stands as, with the names either is written under taken off, which is the account the
     * term is made under ({@link NumericTerm.TakenOver#of}).
     */
    private static ElementProjection placeStanding(ElementValue computed, ElementAnswer closure,
                                                   TermPath at, InputDomain inputs,
                                                   RuleReadingSource source) {
        ElementProjection place = computed.asAPlace();
        if (place == null) {
            return null;
        }
        Type fieldType = inputs.typeAt(place.from(at), source);
        return fieldType != null && TypeOps.base(closure.body().type(), source.inners())
                .equals(TypeOps.base(fieldType, source.inners())) ? place : null;
    }

    /**
     * The number {@code measured} takes over what a walk computed of each of its elements, or null
     * where the walk answered no such computation this reads.
     *
     * <p>For a closure whose answer is not a place of its element — arithmetic over its fields, or
     * a choice between two of those by a flag it holds. The licence is the one a place answer has:
     * the walk answers one value per element of what it was given, proved before the tree was
     * rewritten, so what is asked here is only what the closure came to.
     */
    private static NumericTerm overWhatWasComputed(NumericMeasures.Measured measured,
                                                   ElementAnswer closure, ElementValue computed,
                                                   TermPath at, RuleReadingSource source) {
        Type each = closure.body().type();
        RunSource over = RunSource.computedOverTheElementsAt(at, computed, each);
        return over == null ? null
                : NumericTerm.TakenOver.of(measured.operation(), over, each, source.inners(),
                        source.symbols());
    }

    /**
     * What the closure the walk handed {@code element} to computed of it, or null where there is no
     * such closure or this reads none of it.
     *
     * <p>Only for a total. What is read of a run computed of each element is the sum of those
     * numbers; a count of a walk's answers is a count of the container it walked, and is read as
     * that.
     */
    private static ElementValue computedOf(NumericMeasures.Measured measured, InputReads where,
                                           BindingId element, RuleReadingSource source) {
        if (!(DefaultBoundOperationFacts.get().takenAs(measured.operation())
                instanceof TakenAs.TheSumOfWhatItHolds)) {
            return null;
        }
        ElementAnswer closure = where.answerAt(element);
        return closure == null ? null
                : ElementValue.read(closure, where.heldByTheBody(), source);
    }

}
