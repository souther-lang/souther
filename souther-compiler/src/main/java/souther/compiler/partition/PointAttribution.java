package souther.compiler.partition;

import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.List;

/**
 * Who can move what settled one point a row is owed at.
 *
 * <p><b>Beside what the point is, and never part of it.</b> Which point a row is owed at is settled
 * by the line and by what stops the region beside it ({@link BorderObligationPoint}); who could move
 * either of those is a fact about the reading's surroundings, and two readings that answer it
 * differently are still one point. Read off the identity instead — the lines that happen to be
 * inside it — a run stopping where a declaration narrowed the position came back owed to the line
 * below it and to nobody else, and the declaration that put the end there was told nothing.
 *
 * <p><b>Two kinds of contributor, because the model has two.</b> A rule wrote a line, and that rule
 * is a clause of a type or a comparison in a body ({@link AuthoredLine}); or a declaration took in
 * where a position stops, which is not a line of its own and is named by the reading that placed the
 * end. What a reader asks of either is the same two questions: whether every one of them is a
 * declaration, and which of them are one module's.
 *
 * @param lines     the rules that drew what settled this point
 * @param narrowers the declarations that took in where the position stops, where that is what stops
 *                  the region
 */
public record PointAttribution(List<AuthoredLine> lines, List<TypeSymbol.AtModule> narrowers) {

    /** Nobody: what an end of the order is settled by. */
    public static final PointAttribution NONE = new PointAttribution(List.of(), List.of());

    public PointAttribution {
        lines = List.copyOf(lines);
        narrowers = List.copyOf(narrowers);
    }

    /** One rule's. */
    public static PointAttribution by(AuthoredLine line) {
        return new PointAttribution(List.of(line), List.of());
    }

    /** The declarations that took in where a position stops. */
    public static PointAttribution byNarrowing(List<TypeSymbol.AtModule> narrowers) {
        return new PointAttribution(List.of(), narrowers);
    }

    /**
     * This and {@code also} together, each contributor once.
     *
     * <p>What a point's own line and what stops the region beside it come to, and what two readings
     * of one point come to over the readings. A contributor named twice is one contributor: what
     * counts these is what says how many places a finding about the point names.
     */
    public PointAttribution and(PointAttribution also) {
        List<AuthoredLine> both = new ArrayList<>(lines);
        also.lines.stream().filter(each -> !both.contains(each)).forEach(both::add);
        List<TypeSymbol.AtModule> declarations = new ArrayList<>(narrowers);
        also.narrowers.stream().filter(each -> !declarations.contains(each))
                .forEach(declarations::add);
        return new PointAttribution(both, declarations);
    }

    /**
     * Whether everything that settled this point is a declaration's.
     *
     * <p>Which is what says whether one row anywhere settles it. A clause of a {@code data} states
     * something about the type wherever the type is carried, so a row at a point settled only by
     * clauses is evidence about the type; a comparison is written in a body and states something
     * about that body, so a run that stops at one exists in that body and nowhere else.
     *
     * <p>A declaration that took an end in is a declaration, and an end of the order is nobody's —
     * neither makes a point a body's.
     */
    public boolean owedToDeclarations() {
        return lines.stream().noneMatch(each -> each.obligationOwners().isEmpty());
    }

    /**
     * The declarations of {@code module} that owe a row here, in the order they were contributed.
     *
     * <p>This module's own and not everything that settled the point. What settled it can be several
     * modules' — a line one module wrote, stopped where another module's declaration takes the
     * position in — and a report of this module naming a foreign declaration would be telling its
     * author to go and change somebody else's source. Each module's account names its own
     * ({@link AuthoredLine#ownersIn}).
     */
    public List<TypeSymbol.AtModule> ownersIn(String module) {
        List<TypeSymbol.AtModule> out = new ArrayList<>();
        for (AuthoredLine each : lines) {
            each.ownersIn(module).stream().filter(owner -> !out.contains(owner)).forEach(out::add);
        }
        narrowers.stream()
                .filter(each -> module.equals(each.module()) && !out.contains(each))
                .forEach(out::add);
        return List.copyOf(out);
    }
}
