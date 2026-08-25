package souther.compiler.check;

import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * The lines one declaration draws, in the terms the declaration writes them.
 *
 * <p>What a report calls a line where it prints it under the declaration rather than under a
 * behavior. {@code UserId}'s clause draws {@code String.length(value) = 1}; the behaviors carrying
 * the type meet that line at {@code String.length(draft.owner)} and at
 * {@code String.length(activities[*]@CallTask.owner)}, and neither of those is what the author
 * wrote. A debt named after one of them would be named after whichever reading a report happened to
 * reach first (issue #1062).
 *
 * <p><b>Asked of the declaration, rather than carried from the readings.</b> Which number a clause
 * bounds is read from whatever value the reading started at — {@code Day}'s clause is about
 * {@code value} read from {@code Day} and about {@code d} read from the {@code Span} holding it —
 * so a coordinate that travelled here with a measurement would be one frame of several and nothing
 * would say which. Read from the declaration, there is one frame and it is the author's.
 *
 * <p>Nothing here is an identity. What tells one authored line from another is the clause and which
 * of its conjuncts drew the end ({@link souther.compiler.partition.BorderObligationId}), and that is
 * what this is keyed by; what it hands back is what to call the line. Held as part of the identity,
 * the frames above would make one line two.
 */
public record DeclaredBorders(Map<Key, FieldDomains.Coordinate> forms) {

    /** Which authored line: the clause, and which of its conjuncts placed the end. */
    public record Key(RuleRef.Invariant rule, int conjunct) {}

    /** Nothing was written on the declaration, or it is not one this can read. */
    public static final DeclaredBorders NONE = new DeclaredBorders(Map.of());

    public DeclaredBorders {
        forms = Map.copyOf(forms);
    }

    /**
     * The lines {@code declaredOn} draws.
     *
     * <p>The declaration's own reading of its own rules, which is the reading whose frame is the
     * author's. One of these serves every debt of one declaration, so a caller printing a report
     * asks once per declaration rather than once per line.
     */
    public static DeclaredBorders of(TypeSymbol declaredOn, Symbols symbols, ReadingPolicy policy) {
        Map<Key, FieldDomains.Coordinate> forms = new LinkedHashMap<>();
        for (FieldDomains.Placed placed : Rules.of(declaredOn, symbols, policy).bounds().placed()) {
            // A clause reaching this declaration through a spread is written on another one and is
            // that one's to name, the way a line is named by the rule that drew it (ADR-0090). Its
            // own reading answers for it.
            if (placed.from().clause().id().declaredOn().equals(declaredOn)) {
                forms.put(new Key(placed.from(), placed.conjunct()), placed.at());
            }
        }
        return forms.isEmpty() ? NONE : new DeclaredBorders(forms);
    }

    /**
     * What the author wrote the line on, or null where this declaration draws no such line.
     *
     * <p>Null is an answer about the reading and not about the line: a clause whose end this could
     * not read is a clause with no form to print, and a caller handed one has nothing to call the
     * line but the rule's own name.
     */
    public FieldDomains.Coordinate at(RuleRef.Invariant rule, int conjunct) {
        return forms.get(new Key(rule, conjunct));
    }
}
