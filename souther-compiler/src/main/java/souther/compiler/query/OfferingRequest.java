package souther.compiler.query;

/**
 * What one run was asked to offer rows for.
 *
 * <p>Everything that decides which rows a run composes, said in one value. Which readings it may
 * walk is one half ({@link GenerationScope}) and whether it was asked about the lines a model draws
 * is the other, and a request stating only the first cannot tell two runs apart that offer different
 * rows: the lines are searched for one of them and not the other, so a reader handed the answer
 * would have no way of knowing which question it answers.
 *
 * <p>Said by the caller before anything is asked, for the reason the scope is. What a run offers
 * follows from what was asked for, and a request that read either half back off what some earlier
 * caller happened to have paid for would answer differently depending on the order the requests
 * arrived in.
 *
 * @param module     the module the rows are about
 * @param scope      which readings of a declaration's line this request searches
 * @param boundaries whether the rows at the lines a model draws were asked for
 */
public record OfferingRequest(String module, GenerationScope scope, boolean boundaries) {

    public OfferingRequest {
        if (module == null || scope == null) {
            throw new IllegalArgumentException("a request for rows is about a module, over some"
                    + " readings of it: " + module + " " + scope);
        }
    }

    /** What a caller printing a block for the whole module asks: every reading of it. */
    public static OfferingRequest overTheModule(String module, boolean boundaries) {
        return new OfferingRequest(module, new GenerationScope.Module(), boundaries);
    }

    /** Whether {@code behavior}'s own rows are part of what this asks for. */
    public boolean admits(String behavior) {
        return scope.admits(behavior);
    }
}
