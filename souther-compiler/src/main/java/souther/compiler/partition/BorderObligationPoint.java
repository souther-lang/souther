package souther.compiler.partition;

/**
 * One thing a row is owed for: a point of a line the author wrote, once, however many positions
 * carry it.
 *
 * <p>The unit everything downstream accounts in — what a finding is about, what a verdict counts,
 * what a generated row answers. A line is owed by whoever wrote it ({@link BorderObligationId}) and
 * asks something different at each of its points, so neither half identifies the work on its own: a
 * row at the line and a row beside it are two values and two pieces of work.
 *
 * <p><b>And beside the line, what stopped the region is part of it too.</b> A point against the line
 * names a value of the quantity, and the line settles that value wherever it is read — one debt,
 * whichever position met it. A point away from it names a region, and where a region stops is
 * settled by the line together with whatever bounds it on the far side; so two readings of one line
 * are owed one row there only where the far side is the same thing, and that is what
 * {@link RegionBasis} carries. Keyed on the line alone, a run stopping at a body's own comparison
 * and a run running to the end of the order were one debt and could not both be answered.
 *
 * <p><b>Not where it was read.</b> Which position of which behavior met the line is an occurrence,
 * and it is evidence: it says a row was looked for and what became of it. Held here, one clause of a
 * type is asked for once per position of every behavior carrying it.
 */
public sealed interface BorderObligationPoint {

    /** Which line of the model a row here is owed for. */
    BorderObligationId line();

    /** Which of the four points of it. */
    PointRole role();

    /**
     * Every line of the model this point is owed for: the border's own, and whatever else settled
     * the region beside it.
     *
     * <p>A point at the line is one line's. A run beside it is that line's and the far side's at
     * once — an author can move either and the run moves with it — so a row inside it answers for
     * both. An end the rules leave together and an end of the order are nobody's line, and add
     * none.
     */
    default java.util.List<AuthoredLine> authors() {
        AuthoredLine own = line().line();
        if (!(this instanceof InRegion region)) {
            return java.util.List.of(own);
        }
        return region.region() instanceof RegionBasis.Beside(FarEnd.AtALine far)
                ? java.util.List.of(own, far.line()) : java.util.List.of(own);
    }

    /**
     * Whether every line this point is owed for is a declaration's.
     *
     * <p>Which is what says whether one row anywhere settles it. A clause of a {@code data} states
     * something about the type wherever the type is carried, so a row at a point owed only to
     * clauses is evidence about the type; a comparison is written in a body and states something
     * about that body, so a run that stops at one exists in that body and nowhere else.
     */
    default boolean owedToDeclarations() {
        return authors().stream().noneMatch(each -> each.obligationOwners().isEmpty());
    }

    /**
     * The declarations of {@code module} that owe a row here, in the order the lines name them.
     *
     * <p>The union over what this point is owed for, because each of them owes it: a run bounded by
     * one declaration's clause and another's is both of theirs, and taking either away moves it.
     * Empty where none of them is this module's, which is a point this module keeps no account of
     * ({@link AuthoredLine#ownersIn}).
     */
    default java.util.List<souther.compiler.types.TypeSymbol.AtModule> ownersIn(String module) {
        java.util.List<souther.compiler.types.TypeSymbol.AtModule> out = new java.util.ArrayList<>();
        for (AuthoredLine each : authors()) {
            for (souther.compiler.types.TypeSymbol.AtModule owner : each.ownersIn(module)) {
                if (!out.contains(owner)) {
                    out.add(owner);
                }
            }
        }
        return java.util.List.copyOf(out);
    }

    /**
     * A row at the line itself.
     *
     * <p>Whether a row standing at length 1 is believed is a question about the type and not about
     * any body carrying it, so one row anywhere settles it.
     */
    record AtLine(BorderObligationId line, PointRole role) implements BorderObligationPoint {

        public AtLine {
            if (line == null) {
                throw new IllegalArgumentException("a point is some authored line's");
            }
            if (role == null || !role.againstTheLine()) {
                throw new IllegalArgumentException(
                        "a point at the line is one of the two against it, and " + role
                                + " is a region beside it");
            }
        }
    }

    /**
     * A row in the region on one side of the line, as far as {@code region} stops it.
     *
     * @param region what settled the region beside the line, which is what tells this from the same
     *               point of the same line where something else stopped it
     */
    record InRegion(BorderObligationId line, PointRole role, RegionBasis region)
            implements BorderObligationPoint {

        public InRegion {
            if (line == null || region == null) {
                throw new IllegalArgumentException(
                        "a region a row is owed in is some line's, and stops somewhere: " + line
                                + " " + region);
            }
            if (role == null || role.againstTheLine()) {
                throw new IllegalArgumentException("a point in a region is one of the two beside"
                        + " the line, and " + role + " is at it");
            }
        }
    }
}
