package souther.compiler.inputs;

import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Symbols;

import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;

/**
 * One behavior's input as it was read: where its positions are, what its rules leave the numbers at
 * them, and the names both were read against.
 *
 * <p><b>One value because the three are one reading.</b> Which position a name stands at is the
 * first's to say and what a number there is measured on is the second's, and a reader that holds
 * both uses them together — a term made against one reading and measured on another passes every
 * question either of them asks about itself. Two behaviors can take a parameter spelled the same
 * way, so the term is under a root the second reading has, and what comes back is the order of a
 * position the reader is not asking about. Handed as three arguments, that pairing is the caller's
 * to keep; handed as this, there is nothing to keep.
 *
 * <p>The names are here for the same reason. What a name means is theirs to say, and the quantities
 * were made against one particular answer to that — so the same positions read under another
 * library, or another set of aliases, are a different reading of the same declarations.
 *
 * <p><b>Made by {@link InputDomain#reading} and by nothing else</b>, which is what makes the parts
 * agree. A constructor a caller could reach would be somewhere to put three values back together,
 * and there would be nothing to say they came from one reading — which is the state this exists to
 * remove rather than to check for.
 */
public final class InputReading {

    private final InputDomain domain;
    private final Quantities quantities;
    private final RuleReadingSource rules;
    private final Map<Class<?>, Object> derived = new HashMap<>();

    InputReading(InputDomain domain, Quantities quantities, RuleReadingSource rules) {
        if (domain == null || quantities == null) {
            throw new IllegalArgumentException(
                    "an input is read as its positions and what its rules leave them");
        }
        this.domain = domain;
        this.quantities = quantities;
        this.rules = rules;
    }

    /**
     * What {@code make} works out of this reading, worked out once for it and kept with it.
     *
     * <p>For what is a function of this reading alone and asked by several readers of it. Kept by
     * each reader for itself, it is worked out once per reader, and the readers of one input are
     * many; kept here, it is worked out once for the reading they share. One value of each kind,
     * so {@code make} is the one way of working that kind out.
     *
     * <p>What is kept here is the answer of a question that its key and this reading settle, and
     * that is asked of no reader's state: a question worked out by a function of them, or by a
     * reader made for the question and for nothing else. It is not a reading in the middle of a
     * reader that has met elements, been told what a candidate says, or carries a walk's names:
     * what the reader is left with is part of what such a reading comes to, and one kept here and
     * taken by another reader is taken where that is not the same, and leaves out what it left.
     * Those are kept inside the reader, compared with the state they were made in and told again
     * ({@code SharedReads}, {@code Pullback#kept}).
     *
     * <p>Readers of one input ask from more than one thread, so what {@code make} makes is safe to
     * be asked by several at once.
     */
    public synchronized <T> T derived(Class<T> kind, Function<InputReading, T> make) {
        Object kept = derived.get(kind);
        if (kept == null) {
            kept = make.apply(this);
            derived.put(kind, kept);
        }
        return kind.cast(kept);
    }

    /** Where this input's positions are and what stands at each of them. */
    public InputDomain domain() {
        return domain;
    }

    /** What the rules reaching them leave the numbers there. */
    public Quantities quantities() {
        return quantities;
    }

    /** What the declarations put at a path of this input, read under the same source
     *  ({@link InputDomain#declared}). */
    public DeclaredInput declared() {
        return domain.declared(rules);
    }

    /** The scope and the clause representation the two were read against. */
    public RuleReadingSource rules() {
        return rules;
    }

    /**
     * The world the two were read in, for a reader going on to read the declarations they reach:
     * the same rules under the same budget, borrowing what this reading's own walk made of them.
     */
    public RuleReadingContext ruleReading() {
        return RuleReadingContext.of(rules, domain.policy(), domain.machines(), domain.today());
    }

    /** The names the two were read against. */
    public Symbols symbols() {
        return rules.symbols();
    }

    /** Which declarations wear one value, which is what says whether reading a field reaches
     *  somewhere else ({@link souther.compiler.check.Location#isStep}). */
    public DeclarationNewtypes newtypes() {
        return rules.newtypes();
    }
}
