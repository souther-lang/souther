package souther.compiler.crossing;

/**
 * A value whose whole comparison between two builds may be left to the equality it is compared by.
 *
 * <p>What holds two builds' declarations together reads a form by taking it apart, unless it has
 * nothing of its own to say about one — and then it hands the two over to be compared as written
 * values. That is sound exactly while the equality it hands them to answers what taking them apart
 * would have answered, and that is a claim about the value, made here by whoever wrote it.
 *
 * <p><b>Said, because it cannot be worked out.</b> Read off whether the comparison takes a form
 * apart, the claim is the rule that chose to hand it over, restated: it holds for every form that
 * is handed over, including the one whose equality reads less than its parts do, and a check built
 * on it cannot come out false. So the form says it, and a form that says nothing is one nobody has
 * decided about — which is what a sweep over these reports.
 *
 * <p><b>Not the equality of the form.</b> What it is handed to reads a written number by what the
 * language says two written numbers are, so a decimal written two ways is one value there and two
 * to that class's own {@code equals}. What is claimed is about the comparison that is actually
 * asked for, and a value held in a collection is asked a different one — which is a second claim,
 * about a second equality, and is not this.
 *
 * <p>Every value saying it has nothing inside — each is one of a closed set of cases, written as an
 * enum, or a type the platform declares and this comparison speaks for. A value with a
 * representation to name is taken apart instead, that being what having one means, so the claim
 * made here is never the one standing between a comparison and parts somebody could have read.
 */
public interface DelegatedEqualityIsTheCrossingAnswer {
}
