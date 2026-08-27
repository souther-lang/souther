package souther.compiler.partition;

import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.List;

/**
 * What settled one point a row is owed at, gathered as the reading works it out.
 *
 * <p>Evidence and not the answer read off it. A point is settled by its own line and by whatever
 * stops the region beside it, and those arrive one at a time — so this is the value that can be
 * added to, and whose account the point falls in is asked of the whole of it once it is complete
 * ({@link PointAttribution}). Asked of a part, the answer would be about whichever contributor had
 * arrived.
 *
 * <p><b>Two kinds of contributor, because the model has two.</b> A rule wrote a line, and that rule
 * is a clause of a type or a comparison in a body ({@link AuthoredLine}); or a declaration took in
 * where a position stops, which is not a line of its own and is named by the reading that placed the
 * end.
 *
 * <p><b>Beside what the point is, and never part of it.</b> Which point a row is owed at is settled
 * by the line and by what stops the region beside it ({@link BorderObligationPoint}); who could move
 * either of those is a fact about the reading's surroundings, and two readings that answer it
 * differently are still one point.
 *
 * @param lines     the rules that drew what settled this point
 * @param narrowers the declarations that took in where the position stops, where that is what stops
 *                  the region
 */
public record PointContributions(List<AuthoredLine> lines, List<TypeSymbol.AtModule> narrowers) {

    private static final PointContributions NONE = new PointContributions(List.of(), List.of());

    public PointContributions {
        lines = List.copyOf(lines);
        narrowers = List.copyOf(narrowers);
    }

    /**
     * Nothing yet: what an end of the order is settled by, and what a claim about it carries.
     *
     * <p>Not a point owed to nobody. A claim on its own is one contributor's worth of an answer, and
     * the point it is part of is settled by the line the region lies beside as well — so what
     * reaches {@link PointAttribution} is this together with that line, and this alone is refused
     * there rather than classified as one side or the other.
     */
    public static PointContributions none() {
        return NONE;
    }

    /** One rule's. */
    public static PointContributions by(AuthoredLine line) {
        return new PointContributions(List.of(line), List.of());
    }

    /**
     * The declarations that took in where a position stops, read off the end they took in.
     *
     * <p>The end and not the names. This is where they stop being held against one and start being
     * what a report writes back, and it is the last step of the way they came: a reading answered
     * that they are about that end, the lowering kept which end it was, and the caller has just
     * found that the run stops at the place it lowers onto. Taking the names instead would let a
     * caller that skipped any of those write them down all the same.
     */
    static PointContributions byNarrowing(DomainEnd leaves) {
        return leaves.attribution() == null ? NONE
                : new PointContributions(List.of(), leaves.attribution().names());
    }

    /** Whether nothing has contributed, which is a value nothing can be concluded from. */
    public boolean isEmpty() {
        return lines.isEmpty() && narrowers.isEmpty();
    }

    /**
     * This and {@code also} together, each contributor once.
     *
     * <p>What a point's own line and what stops the region beside it come to. A contributor named
     * twice is one contributor: what counts these is what says how many places a finding about the
     * point names.
     */
    public PointContributions and(PointContributions also) {
        List<AuthoredLine> both = new ArrayList<>(lines);
        also.lines.stream().filter(each -> !both.contains(each)).forEach(both::add);
        List<TypeSymbol.AtModule> declarations = new ArrayList<>(narrowers);
        also.narrowers.stream().filter(each -> !declarations.contains(each))
                .forEach(declarations::add);
        return new PointContributions(both, declarations);
    }

    /**
     * Whether everything that contributed is a declaration's.
     *
     * <p>A clause of a {@code data} states something about the type wherever the type is carried, so
     * a row at a point settled only by clauses is evidence about the type; a comparison is written
     * in a body and states something about that body, so a run that stops at one exists in that body
     * and nowhere else.
     *
     * <p>A declaration that took an end in is a declaration, and an end of the order contributes
     * nothing — neither makes a point a body's. Asked of a value nothing has contributed to, this
     * answers vacuously, which is why {@link PointAttribution} refuses that value rather than
     * reading this.
     */
    boolean allDeclarations() {
        return lines.stream().noneMatch(each -> each.obligationOwners().isEmpty());
    }

    /**
     * The declarations that owe a row here, in the order they contributed.
     *
     * <p>Every one of them, whichever module wrote it. What settled a point can be several modules' —
     * a line one module wrote, stopped where another module's declaration takes the position in —
     * and which of them a module answers for is that module's account to decide
     * ({@link PointAttribution.TheDeclarations#ownersIn}).
     */
    List<TypeSymbol.AtModule> owners() {
        List<TypeSymbol.AtModule> out = new ArrayList<>();
        for (AuthoredLine each : lines) {
            each.obligationOwners().stream().filter(owner -> !out.contains(owner))
                    .forEach(out::add);
        }
        narrowers.stream().filter(each -> !out.contains(each)).forEach(out::add);
        return List.copyOf(out);
    }
}
