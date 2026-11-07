package souther.compiler.partition;

import souther.compiler.observe.RunSensitivity;

import java.util.Collections;
import java.util.EnumMap;
import java.util.EnumSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Supplier;

/**
 * The figure each of this compiler's budgets is held to in one compilation: the one declared
 * ({@link CompositionBudget#declared}), where nothing else is said for it, and the one said here
 * where something is.
 *
 * <p>Which is what makes a wider run a run somebody can ask for
 * ({@link RunSensitivity#MAY_CHANGE}), and a narrower one too: a figure set lower
 * stops a walk sooner, which is how a reader of what a stop says is shown one with a model small
 * enough to read.
 *
 * <p><b>For a whole compilation, and in force while it answers.</b> Every answer a compilation
 * keeps was worked out under the figures it was set up with, and nothing it keeps notices a figure
 * changing; so they are said once, before anything is asked ({@code Db#allowing}), and are in force
 * for every question it answers. A figure read outside any compilation's answering is the one
 * declared.
 *
 * <p><b>And carried, where a figure is reached.</b> What stopped at a figure says the number it
 * stood at ({@link CompositionBudget#figure}), made where the figure was reached and so under the
 * compilation reaching it, and a reader is told that number however long after. A reader putting
 * figures together out of the budgets an answer names does so under the compilation's figures as
 * well ({@code AdequacyReport#of}).
 */
public final class Allowances {

    /** Every figure as declared. */
    public static final Allowances DECLARED = new Allowances(Map.of());

    /**
     * The budgets a compilation may hold to another figure: those every reader asks for its
     * figure where it uses it.
     *
     * <p>A class that copies a figure into a constant of its own when it is loaded holds the one in
     * force then, which is the one declared, for every compilation after; another figure said for
     * it would be said and not held. So only these are, and a figure said for any other budget is
     * refused rather than left unheld. That no class copies one of these is held of the compiled
     * code ({@code AFigureACompilationSetsIsReadWhereItIsUsedTest}).
     */
    public static final Set<CompositionBudget> SETTABLE = Collections.unmodifiableSet(
            EnumSet.of(CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO));

    private static final ScopedValue<Allowances> IN_FORCE = ScopedValue.newInstance();

    private final Map<CompositionBudget, Integer> figures;

    private Allowances(Map<CompositionBudget, Integer> figures) {
        this.figures = figures;
    }

    /**
     * These, with {@code budget} held to {@code figure}.
     *
     * @throws IllegalArgumentException where {@code budget} is not one of {@link #SETTABLE}
     */
    public Allowances with(CompositionBudget budget, int figure) {
        Objects.requireNonNull(budget, "a figure is some budget's");
        if (!SETTABLE.contains(budget)) {
            throw new IllegalArgumentException(budget + " is copied where it is read, and would"
                    + " be held to " + budget.declared() + " whatever is said for it");
        }
        if (figure < 0) {
            throw new IllegalArgumentException("a figure is no fewer than none: " + figure);
        }
        Map<CompositionBudget, Integer> out = new EnumMap<>(CompositionBudget.class);
        out.putAll(figures);
        if (figure == budget.declared()) {
            out.remove(budget);
        } else {
            out.put(budget, figure);
        }
        return new Allowances(out.isEmpty() ? Map.of() : Collections.unmodifiableMap(out));
    }

    /** The figure {@code budget} is held to under these. */
    public int of(CompositionBudget budget) {
        Integer said = figures.get(budget);
        return said == null ? budget.declared() : said;
    }

    /**
     * Whether these are the figures read where this is asked: these themselves in force, or
     * nothing in force and these the ones declared. A store asks it before every question, so it
     * asks the one in force by identity, which a store's own figures are wherever it answers.
     */
    public boolean inForce() {
        return IN_FORCE.isBound() ? IN_FORCE.get() == this : figures.isEmpty();
    }

    /** What {@code work} comes to with these in force. */
    public <T> T over(Supplier<T> work) {
        return ScopedValue.where(IN_FORCE, this).call(work::get);
    }

    /** The figure {@code budget} is held to where it is read: the one in force, or the one
     *  declared. */
    static int inForce(CompositionBudget budget) {
        return IN_FORCE.isBound() ? IN_FORCE.get().of(budget) : budget.declared();
    }

    @Override
    public boolean equals(Object other) {
        return this == other || (other instanceof Allowances allowances
                && figures.equals(allowances.figures));
    }

    @Override
    public int hashCode() {
        return figures.hashCode();
    }

    @Override
    public String toString() {
        return figures.isEmpty() ? "as declared" : figures.toString();
    }
}
