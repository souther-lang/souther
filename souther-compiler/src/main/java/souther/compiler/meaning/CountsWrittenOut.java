package souther.compiler.meaning;

import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.WeakHashMap;

/**
 * A statement with every count of statements in it written out as the choices of which of them
 * hold, for one reader that takes a statement apart as conjunctions and disjunctions and has no
 * reading of a count of its own — or the figure the writing out stopped at.
 *
 * <p>The one place such a reader is handed choices. Held to figures by what the reader is handed
 * in all, and not count by count: a statement holding two counts each within the figures could
 * otherwise come to twice what any one is held to. Each count is handed no more choices than one
 * condition is read in, and every count in the statement together no more parts than
 * {@link CompositionBudget#PARTS_THE_CHOICES_OF_A_COUNT_COME_TO}. A count's choices are written out
 * once, and charged to every reader they are handed to, which walks them each time.
 *
 * <p>What a search reaches is written out too, so no count is left anywhere a reader goes.
 */
public final class CountsWrittenOut {

    private static final CompositionBudget PARTS =
            CompositionBudget.PARTS_THE_CHOICES_OF_A_COUNT_COME_TO;

    /** What a reader is handed. */
    public sealed interface Handed permits Written, PastAFigure {}

    /** {@code stated} with no count left in it. */
    public record Written(Proposition stated) implements Handed {

        public Written {
            Objects.requireNonNull(stated, "something is handed");
        }
    }

    /** No statement, the counts in it written out being past {@code figure}. */
    public record PastAFigure(CompositionBudget figure) implements Handed {

        public PastAFigure {
            Objects.requireNonNull(figure, "a writing out stops at some figure");
        }
    }

    /**
     * What each statement was handed as, kept while the statement is held: every reader asks where
     * a statement enters it, and some of them are asked of one statement again and again. A
     * statement handed as itself is kept as nothing and not as itself, which the entry holding it
     * would keep from ever being let go.
     */
    private static final Map<Proposition, Optional<Handed>> HANDED = new WeakHashMap<>();

    /** The same, for a reader that reads a count itself wherever it stands outside an element of a
     *  container ({@link #outsideElementsOf}). */
    private static final Map<Proposition, Optional<Handed>> HANDED_OUTSIDE_ELEMENTS =
            new WeakHashMap<>();

    private long partsLeft = PARTS.maximum();
    private CompositionBudget stoppedAt;
    /** Whether a count outside every element of a container is left as it is. */
    private boolean leavingCounts;

    private CountsWrittenOut(boolean leavingCounts) {
        this.leavingCounts = leavingCounts;
    }

    /** What {@code stated} is handed to such a reader as. */
    public static Handed of(Proposition stated) {
        return of(stated, false, HANDED);
    }

    /**
     * What {@code stated} is handed to a reader that reads a count of statements itself, as far as
     * it can: a count is left as it is wherever it stands outside the element of a container, and
     * written out inside one, where the statements are met by each element apart.
     *
     * <p>A count whose statements are themselves counts inside an element is written out whole.
     */
    public static Handed outsideElementsOf(Proposition stated) {
        return of(stated, true, HANDED_OUTSIDE_ELEMENTS);
    }

    private static Handed of(Proposition stated, boolean leavingCounts,
                             Map<Proposition, Optional<Handed>> handedBefore) {
        synchronized (handedBefore) {
            Optional<Handed> kept = handedBefore.get(stated);
            if (kept != null) {
                return kept.orElseGet(() -> new Written(stated));
            }
        }
        CountsWrittenOut writing = new CountsWrittenOut(leavingCounts);
        Proposition written = writing.writtenOut(stated);
        Handed handed = written == null ? new PastAFigure(writing.stoppedAt) : new Written(written);
        synchronized (handedBefore) {
            handedBefore.putIfAbsent(stated,
                    written == stated ? Optional.empty() : Optional.of(handed));
        }
        return handed;
    }

    /** {@code stated} written out, or null where the writing stopped. */
    private Proposition writtenOut(Proposition stated) {
        return switch (stated) {
            case Proposition.SoManyHold counted when leavingCounts && leaves(counted) -> counted;
            case Proposition.SoManyHold counted -> {
                WhichOfThemHold.Written written = counted.writtenForAReader();
                if (written.choices() == null) {
                    yield stop(written.stoppedAt());
                }
                if (written.parts() > partsLeft) {
                    yield stop(PARTS);
                }
                partsLeft -= written.parts();
                yield writtenOut(written.choices());
            }
            // The cases it is written out as are walked by whoever it is handed to, so they are
            // held to what a reader is handed in all, as the choices of a count are.
            case Proposition.OfTheWays ways -> {
                long cases = ways.ways().cases();
                if (cases > partsLeft) {
                    yield stop(PARTS);
                }
                partsLeft -= cases;
                yield writtenOut(ways.written());
            }
            case Proposition.All all -> {
                List<Proposition> parts = writtenOut(all.parts());
                yield parts == null ? null : parts == all.parts() ? all : Proposition.all(parts);
            }
            case Proposition.WhereItAnswers where -> {
                Proposition answers = writtenOut(where.answers());
                Proposition states = answers == null ? null : writtenOut(where.states());
                yield states == null ? null
                        : answers == where.answers() && states == where.states() ? where
                        : Proposition.whereItAnswers(answers, states);
            }
            case Proposition.Any any -> {
                List<Proposition> parts = writtenOut(any.parts());
                yield parts == null ? null : parts == any.parts() ? any : Proposition.any(parts);
            }
            case Proposition.OnAnApplication applications -> {
                List<Proposition> each = writtenOut(applications.each());
                yield each == null ? null : each == applications.each() ? applications
                        : Proposition.onAnApplication(each);
            }
            case Proposition.Some some -> {
                Proposition element = writtenOutInAnElement(some.ofTheElement());
                yield element == null ? null : element == some.ofTheElement() ? some
                        : new Proposition.Some(some.container(), element, some.holds());
            }
            case Proposition.SomeReachable reached -> {
                Proposition atANode = writtenOutInAnElement(reached.atANode());
                if (atANode == null) {
                    yield null;
                }
                Proposition noneBelow = reached.noneBelow().isEmpty() ? null
                        : writtenOutInAnElement(reached.noneBelow().get());
                if (reached.noneBelow().isPresent() && noneBelow == null) {
                    yield null;
                }
                yield atANode == reached.atANode()
                        && (noneBelow == null || noneBelow == reached.noneBelow().get()) ? reached
                        : new Proposition.SomeReachable(reached.at(), reached.writtenAt(),
                                reached.through(), atANode,
                                reached.noneBelow().map(_ -> noneBelow), reached.holds());
            }
            case Proposition.Always _, Proposition.Compared _, Proposition.Truth _,
                 Proposition.InCases _, Proposition.Present _, Proposition.InTheStrings _,
                 Proposition.SameValue _, Proposition.LastToHold _, Proposition.Carried _,
                 Proposition.Unread _ -> stated;
        };
    }

    /** Whether no count stands inside an element of a container in the statements of
     *  {@code counted}, outside which a count is left as it is. */
    private static boolean leaves(Proposition.SoManyHold counted) {
        return new CountsWrittenOut(true).writtenOut(counted.statements()) == counted.statements();
    }

    /** {@code stated}, which an element of a container meets, written out: every count in it is
     *  met by each element apart. */
    private Proposition writtenOutInAnElement(Proposition stated) {
        boolean leaving = leavingCounts;
        leavingCounts = false;
        try {
            return writtenOut(stated);
        } finally {
            leavingCounts = leaving;
        }
    }

    /** Each of {@code parts} written out, the list itself where none changed, or null where one
     *  could not be. */
    private List<Proposition> writtenOut(List<Proposition> parts) {
        List<Proposition> out = new ArrayList<>(parts.size());
        boolean changed = false;
        for (Proposition part : parts) {
            Proposition written = writtenOut(part);
            if (written == null) {
                return null;
            }
            changed |= written != part;
            out.add(written);
        }
        return changed ? out : parts;
    }

    private Proposition stop(CompositionBudget figure) {
        stoppedAt = figure;
        return null;
    }
}
