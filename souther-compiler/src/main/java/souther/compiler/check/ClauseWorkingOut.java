package souther.compiler.check;

/**
 * What a run needs of the numbers to get through working a clause out, read over the shape the
 * clause was written in ({@link ClauseExpr}).
 *
 * <p>Over the shape, so that a binding, a denial and a helper that restates one are crossed as every
 * other reading of a clause crosses them: a sum under {@code Bool.not(...)} or inside a name given a
 * value is worked out where the clause is, and a reading of its own that walked the tree would find
 * the ones it had been taught the spelling of.
 *
 * <p>A conjunction is worked out on both sides wherever it holds. A choice is worked out on its
 * left, and on its right only on the runs the left lets through, which is read off what is known
 * and not off the spelling. Where the left cannot hold ({@link Predicates.Owed#refutedBy}) the
 * right is worked out on every run, and what it asks is asked of them all. Where the left holds on
 * every run ({@link Predicates.Owed#dischargedBy}) the right is worked out on none, and asks
 * nothing. Where either may happen, the right asks what it asks of some runs only: nothing is
 * added, and the reading says that something may be lost ({@link WorkingOutNeeds#onlyOnSomeRuns}).
 *
 * <p>A binding's value is worked out where the binding stands, whether or not the clause under it
 * reads the name ({@link ClauseReading#crossing}).
 */
final class ClauseWorkingOut implements ClauseReading<WorkingOutNeeds, Denotations> {

    private final PathCompletion completion;

    private final Predicates predicates;

    private final Known known;

    private final ClauseScope<Denotations> scope;

    /**
     * @param known what holds where the clause is built, which an ask already held is not repeated
     *              against and a choice's left is refuted by
     * @param scope what a binding changes, as every reading of this clause is given it
     */
    ClauseWorkingOut(PathCompletion completion, Predicates predicates, Known known,
                     ClauseScope<Denotations> scope) {
        this.completion = completion;
        this.predicates = predicates;
        this.known = known;
        this.scope = scope;
    }

    /** What a run needs to work {@code clause} out, held to come to what it states. */
    WorkingOutNeeds of(ClauseExpr clause, Denotations at) {
        return read(clause, at, scope, null);
    }

    @Override
    public Descent<WorkingOutNeeds> at(ClauseExpr.Joined join) {
        return switch (join.how()) {
            case BOTH -> new Descent.Into<>(WorkingOutNeeds::and);
            case EITHER -> new Descent.Whole<>();
        };
    }

    @Override
    public WorkingOutNeeds whole(ClauseExpr.Part part, Denotations at) {
        return switch (part) {
            case ClauseExpr.Leaf leaf -> completion.workedOut(leaf.of(), known, at);
            case ClauseExpr.Joined choice -> {
                WorkingOutNeeds left = of(choice.left(), at);
                Predicates.Owed stated = predicates.assumed(choice.left(), at, false, null);
                if (stated.dischargedBy(known)) {
                    // The left comes to what it states on every run, so the right is never
                    // reached.
                    yield left;
                }
                WorkingOutNeeds right = of(choice.right(), at);
                yield left.and(stated.refutedBy(known) ? right : right.onlyOnSomeRuns());
            }
        };
    }

    /**
     * The value a binding is given, which is worked out where the binding stands and whether or not
     * the clause under it reads the name.
     */
    @Override
    public WorkingOutNeeds crossing(ClauseExpr.Scoped binding, Denotations outside,
                                    WorkingOutNeeds body) {
        WorkingOutNeeds value = completion.workedOut(binding.binding().value(), known, outside);
        return value.and(body).underABindingWhoseValue(value.read());
    }
}
