package souther.compiler.partition;

import souther.compiler.query.Compilation;
import souther.compiler.query.Front;

/**
 * What a compilation sets, for a test standing the search up without one.
 *
 * <p>Asked of a compilation rather than written here. The numbers belong to
 * {@code Front.Adequacy.STANDARD} and are held out of reach of everything that measures a behavior
 * on purpose (rule 4 of this package's documentation) — so a test naming them again would be a
 * second place they are written, free to go on saying two hundred after the one that matters says
 * something else.
 *
 * <p>And asked rather than defaulted. A search handed no budget picking one up is the arrangement
 * the rule exists against; a test is a caller like any other, and this is that caller saying which
 * budget it is using.
 */
public final class Budgets {

    private Budgets() {}

    /** The policy a compilation that says nothing is held to. Built from an empty module, which
     *  sets the inputs in its constructor and compiles nothing. */
    private static final AdequacyPolicy STANDARD = Compilation.ofSource("module example.empty", "Main")
            .db().ask(new Front.Adequacy()).value();

    public static AdequacyPolicy.OfTheGeneration generation() {
        return STANDARD.generation();
    }

    public static AdequacyPolicy.OfTheMeasures measures() {
        return STANDARD.measures();
    }
}
