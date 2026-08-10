package souther.compiler.partition;

import souther.compiler.types.TypeName;

import java.util.Optional;

/**
 * One equivalence class of an input position: a set of values expected to behave the same way.
 *
 * <p>Three things are kept apart that a single "class" would run together — what the class means,
 * how a value is told to be in it, and whether one can be produced. A class whose representative
 * cannot be built is still a class: rows that reach it still count, and only the generator has to say
 * it cannot fill the gap.
 *
 * @param id                a name stable within its axis, used to compare one run against another
 * @param label             what to call it in a report
 * @param classifier        whether a value the rows already carry is in this class
 * @param representatives   values that could stand for it, in the order to try them
 * @param generationFailure why nothing can be produced, when nothing can
 * @param shape             the constructor a value for this class has to be built through, where the
 *                          class has values and cannot name one. A record's fields are chosen one at
 *                          a time against the rules relating them, which is the generator's walk and
 *                          not a list this could hold — so what is held is which constructor, and the
 *                          walk that composes every other record composes this one. Not the position's
 *                          type: the declared type is still the sum, and only the value being built
 *                          is narrowed
 */
public record PartitionClass(String id, String label, Classifier classifier,
                             RepresentativeSource representatives,
                             Optional<String> generationFailure,
                             Optional<TypeName> shape) {

    public PartitionClass {
        generationFailure = generationFailure == null ? Optional.empty() : generationFailure;
        shape = shape == null ? Optional.empty() : shape;
    }

    public PartitionClass(String id, String label, Classifier classifier,
                          RepresentativeSource representatives,
                          Optional<String> generationFailure) {
        this(id, label, classifier, representatives, generationFailure, Optional.empty());
    }

    public static PartitionClass of(String id, String label, Classifier classifier,
                                    RepresentativeSource representatives) {
        return new PartitionClass(id, label, classifier, representatives, Optional.empty());
    }

    /** A class whose values are composed through {@code shape} rather than named here. */
    public static PartitionClass composed(String id, String label, Classifier classifier,
                                          TypeName shape) {
        return new PartitionClass(id, label, classifier, RepresentativeSource.none(),
                Optional.empty(), Optional.of(shape));
    }

    /** A class nothing can produce a value for, and why. */
    public static PartitionClass ungeneratable(String id, String label, Classifier classifier,
                                               String why) {
        return new PartitionClass(id, label, classifier, RepresentativeSource.none(),
                Optional.of(why));
    }

    public boolean generatable() {
        return generationFailure.isEmpty()
                && (shape.isPresent() || !representatives.candidates().isEmpty());
    }
}
