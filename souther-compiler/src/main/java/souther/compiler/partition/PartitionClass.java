package souther.compiler.partition;

import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

/**
 * One equivalence class of an input position: a set of values expected to behave the same way.
 *
 * <p>Three things are kept apart that a single "class" would run together — what the class means,
 * how a value is told to be in it, and whether one can be produced. A class whose representative
 * cannot be built is still a class: rows that reach it still count, and only the generator has to say
 * it cannot fill the gap.
 *
 * @param id              a name stable within its axis, used to compare one run against another
 * @param label           what to call it in a report
 * @param classifier      whether a value the rows already carry is in this class
 * @param representatives how a value standing for it is arrived at
 * @param denotes         the values this class holds, where they can be written out, and null
 *                        where they cannot. A fourth thing, and separate from {@link #classifier}
 *                        for the reason the others are separate: a classifier answers about one
 *                        value, and a reader asking whether a rule refuses the whole class is
 *                        asking about all of them. A case holding a record has no end of values
 *                        and says nothing here; a case of an enumeration is one value and says so.
 *
 *                        <p>Null is "not written out here" and never "holds nothing" — a class
 *                        that holds nothing is not a class of the position, and what decides that
 *                        is the reading this is put to
 */
public record PartitionClass(String id, String label, Classifier classifier,
                             RepresentativeSource representatives, ValueSet denotes) {

    public static PartitionClass of(String id, String label, Classifier classifier,
                                    RepresentativeSource representatives) {
        return new PartitionClass(id, label, classifier, representatives, null);
    }

    /** A class nothing can produce a value for, and why. */
    public static PartitionClass ungeneratable(String id, String label, Classifier classifier,
                                               String why) {
        return new PartitionClass(id, label, classifier,
                new RepresentativeSource.Ungeneratable(why), null);
    }

    /**
     * The same class, saying which values it holds.
     *
     * <p>Written by the producer that knows, since knowing is what it takes to say it: a case of an
     * enumeration is the one value the case is, and a class over a range is not something this can
     * write out. A producer that says nothing leaves a class no rule can be proved to refuse
     * whole, which is the safe direction — the class stays.
     */
    public PartitionClass holding(ValueSet values) {
        return new PartitionClass(id, label, classifier, representatives, values);
    }

    /**
     * Whether {@code admitted} leaves this class a value, where that can be settled.
     *
     * <p>One question and two proofs, which is why it is asked here rather than at each shape a set
     * comes in. {@code admitted} is an upper bound on what the position holds, so a class holding
     * none of a finite set holds nothing at all; and a set written as a denial proves a class empty
     * only by excluding every value the class has, which takes the class knowing what those are.
     * Where neither proof is available the class stays: nothing has shown the position cannot reach
     * it, and a class taken away on less than that is a distinction the model states going missing.
     */
    public boolean leftAnythingBy(ValueSet admitted, java.util.function.Predicate<Value> holds) {
        if (denotes != null) {
            return !denotes.meet(admitted).isEmpty();
        }
        return !(admitted instanceof ValueSet.Finite finite)
                || finite.values().stream().anyMatch(holds);
    }

    public boolean generatable() {
        return representatives.buildable();
    }
}
