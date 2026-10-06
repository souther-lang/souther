package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.TermOrders;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.PlacesApart;
import net.unit8.notation199x.pattern.Meter;
import souther.compiler.types.Type;
import souther.compiler.values.ValueSet;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.function.Supplier;

/**
 * What the lines and the values singled out on one position's order divide it into, together.
 *
 * <p><b>One partition and not one per kind of rule.</b> A line and a value singled out are both
 * distinctions on the order the values are counted on, and the classes are what every one of them
 * leaves at once: the runs between the lines, and out of the run a value falls in, the value and
 * the rest of the run. Chosen between instead — the runs where a line was drawn, the values where
 * none was — a position with both had the classes of one kind, and a decision on the other kind
 * was about a class that did not exist.
 *
 * <p><b>The run is not cut at the value.</b> {@code x == 3 || x >= 10} leaves three, the run below
 * ten without three, and the run from ten up. The values either side of three below ten are ones
 * the model treats alike, and two classes there would ask the rows for a distinction no rule
 * makes.
 *
 * <p>A position no line divides is the same rule with the whole of the order as the one run: each
 * value singled out, and everything else.
 */
final class OrderedClasses {

    private OrderedClasses() {
    }

    /**
     * The classes {@code runs} and {@code points} leave {@code term} divided into, or none where
     * neither divides it.
     *
     * @param runs   the runs the lines leave, as {@link Intervals#of} answers them: none where the
     *               lines leave fewer than two
     * @param within where the rules leave the number
     * @param admits which values the declarations leave standing at the position. Beside
     *               {@code within} and not instead of it: a rule about how many a value holds is
     *               about another number of the same place, and what it leaves is said of the values
     *               rather than of this number — so a representative worked out from the range alone
     *               is one the declarations may refuse
     * @param perWitness what writing one value beside the ones singled out may cost, named by the
     *                   caller that pays for witnesses
     */
    static List<PartitionClass> of(List<Band> runs, List<GuardThresholds.Guards.Singled> points,
                                   NumericTerm.FromOnePosition term, Type type,
                                   Quantities reading, RuleReadingContext ruleReading,
                                   NumericDomain.Bounds within, ValueSet admits,
                                   Supplier<Meter> perWitness) {
        // Asked here rather than handed in beside the term. A term and a pair of orders are two
        // arguments, and two arguments can be about two terms; the reading is one argument that
        // answers about whichever term it is asked.
        TermOrders orders = reading.ordersOf(term);
        Carrier carrier = orders.answered();
        List<Place> values = new ArrayList<>();
        for (GuardThresholds.Guards.Singled each : points) {
            if (values.stream().noneMatch(had -> had.sameAs(each.value()))) {
                values.add(each.value());
            }
        }
        Endpoint min = within == null ? null : within.min();
        Endpoint max = within == null ? null : within.max();
        List<PartitionClass> classes = new ArrayList<>();
        if (runs.isEmpty()) {
            if (!values.isEmpty()) {
                classes.addAll(singledOut(values, orders, type, reading, ruleReading, within,
                        admits, perWitness));
            }
        } else {
            for (Band run : runs) {
                List<Place> taken = values.stream()
                        .filter(each -> run.holds(new Level.OnACarrier(carrier, each))).toList();
                for (Place value : taken) {
                    classes.add(theValue(value, orders, type, reading, ruleReading));
                }
                // The rest of the run, where there is a rest. A run the values taken out of it
                // leave nothing of is those values, and a class beside them holding nothing is one
                // no row is ever counted at.
                if (taken.isEmpty() || anythingLeft(new NumericSet.InARunExcept(run, taken),
                        carrier, min, max)) {
                    classes.add(Intervals.classOf(run, taken, term, type, reading, ruleReading,
                            min, max));
                }
            }
        }
        // Classes of the number the values and the runs are of, said where that is known.
        return classes.stream().map(each -> each.ofTheNumber(term)).toList();
    }

    /**
     * Whether {@code rest} holds a value of the position, asked of the order.
     *
     * <p>Kept where the order could not say: a class nobody can show is empty is one the rows are
     * still owed at, and dropped on a guess it would be a distinction gone missing from the
     * denominator.
     */
    private static boolean anythingLeft(NumericSet rest, Carrier carrier, Endpoint min,
                                        Endpoint max) {
        LevelSpace space = LevelSpace.onACarrier(carrier);
        for (LevelInterval part : Criterion.Within.runsInside(rest.region(carrier), carrier,
                min, max)) {
            if (!(space.inspect(part) instanceof Occupancy.Empty)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Each value singled out of a position no line divides, and everything else.
     *
     * <p>The last of those is not an interval and is not asked to be. What a class needs is a way to
     * say whether a value is in it and a value that stands for it, and a complement has both.
     */
    private static List<PartitionClass> singledOut(List<Place> values, TermOrders orders,
                                                   Type type, Quantities reading,
                                                   RuleReadingContext ruleReading,
                                                   NumericDomain.Bounds within, ValueSet admits,
                                                   Supplier<Meter> perWitness) {
        Carrier carrier = orders.answered();
        List<PartitionClass> classes = new ArrayList<>();
        for (Place value : values) {
            classes.add(theValue(value, orders, type, reading, ruleReading));
        }
        // Out of what writing one value costs, as every witness for a row is. Which number beside
        // the ones singled out to write is chosen here; what a value standing at that number looks
        // like is asked of the one reader that answers it, so the number and the value it is
        // written into are not two spellings of one thing.
        Place other = carrier.somethingOtherThan(PlacesApart.of(values), within, admits,
                perWitness.get());
        String label = "/= " + String.join(", ",
                values.stream().map(carrier::written).toList());
        classes.add(classAt(orders.term().atOnePosition() + "/" + label, label,
                orders, new NumericSet.AwayFrom(values), other, type, reading, ruleReading));
        return classes;
    }

    /** The class that is one value singled out, and nothing else. */
    private static PartitionClass theValue(Place value, TermOrders orders, Type type,
                                           Quantities reading, RuleReadingContext ruleReading) {
        String written = orders.answered().written(value);
        return classAt(orders.term().atOnePosition() + "/= " + written, "= " + written,
                orders, new NumericSet.At(value), value, type, reading, ruleReading);
    }

    /**
     * A class over the values a rule singled out, standing for whatever writes a value at one of
     * those numbers.
     *
     * <p><b>Asked of the one reader that writes a value for a number.</b> A value singled out of a
     * number taken of a position is not a value of the position: the ninth hour is a number and a
     * time is what stands there, and a class that wrote the number itself put a count where the
     * decoder wanted a time.
     */
    private static PartitionClass classAt(String id, String label, TermOrders orders,
                                          NumericSet is, Place at, Type type, Quantities reading,
                                          RuleReadingContext ruleReading) {
        String what = "a value whose " + Intervals.measureOf(orders.term().atOnePosition()) + " is "
                + (is instanceof NumericSet.At ? "the one" : "none of the ones") + " singled out";
        Recognition holding = new Recognition.OfACount(orders.term().atOnePosition(), orders, is);
        if (at == null) {
            // No number was named beside the ones singled out, which is this compiler naming one
            // place in a run and not the order having none left.
            return PartitionClass.of(id, label, holding,
                    new RepresentativeSource.NotArrivedAt(CompositionShortfall.writing(
                            Set.of(CompositionRepertoire.PLACES_IN_A_RUN_THAT_ARE_NAMED)),
                            "nothing here composed " + what
                                    + ", which does not make one unwritable"));
        }
        // The number this reader named, and what stands at it asked of what writes a value for a
        // number. Written here out of the carrier instead, a number taken of the position went into
        // the row where the value it was taken of belongs — a count where a time was owed.
        //
        // The class stays what it is. Asked as the one number named, a class holding every number
        // but the ones a rule singled out would be answered by whichever of them this reader
        // reached for first — and nothing built at that one would be told as a class with no value
        // in it, which is every other number it holds going unlooked at.
        return PartitionClass.of(id, label, holding,
                Intervals.standingFor(orders, is, at, type, reading, ruleReading, what));
    }
}
