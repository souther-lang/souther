package souther.compiler.partition;

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
 */
public record PartitionClass(String id, String label, Classifier classifier,
                             RepresentativeSource representatives) {

    public static PartitionClass of(String id, String label, Classifier classifier,
                                    RepresentativeSource representatives) {
        return new PartitionClass(id, label, classifier, representatives);
    }

    /** A class nothing can produce a value for, and why. */
    public static PartitionClass ungeneratable(String id, String label, Classifier classifier,
                                               String why) {
        return new PartitionClass(id, label, classifier,
                new RepresentativeSource.Ungeneratable(why));
    }

    public boolean generatable() {
        return representatives.buildable();
    }
}
