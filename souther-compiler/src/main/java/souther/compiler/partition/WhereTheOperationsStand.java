package souther.compiler.partition;

import java.util.Objects;

/**
 * What the tree the language's own operations stand in says about the forks of a body, for the
 * reading of the runs, which walks the tree where those operations are expanded and cannot say it.
 *
 * <p>Read by the one walk of the comparisons, and joined to the reading of the runs on the
 * construct of the model the two trees agree about ({@link souther.compiler.types.ModelOccurrence}).
 * Carried as one value from that walk to the readers of it, so that a reader is handed all of it or
 * none.
 *
 * @param armsNamed      the case each arm of a {@code match} is, where the value matched stands at
 *                       a position: an arm the reading of the runs could not name is about that
 *                       position
 * @param dependencies   which positions each construct deciding a fork the reading of the runs
 *                       names no subject for may turn on: what such a fork may tell apart, and
 *                       nothing about how
 * @param oneApplication the forks a run gets to within one application of each closure around them,
 *                       where a way written from where the closure stands leaves out nothing but
 *                       which element the application was handed
 */
public record WhereTheOperationsStand(ArmsNamed armsNamed, ForkDependencies dependencies,
                                      WithinOneApplication oneApplication) {

    /** Of a body no such tree was read for. */
    public static final WhereTheOperationsStand NONE = new WhereTheOperationsStand(
            ArmsNamed.NONE, ForkDependencies.NONE, WithinOneApplication.NONE);

    public WhereTheOperationsStand {
        Objects.requireNonNull(armsNamed, "the arms named, or none");
        Objects.requireNonNull(dependencies, "what the forks turn on, or nothing known");
        Objects.requireNonNull(oneApplication, "the forks within one application, or none");
    }
}
