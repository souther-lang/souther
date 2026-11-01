package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A part put through a statement ({@link WhereEachLineDecides#with}) comes to the statement that
 * making every conjunction, disjunction and statement read where an operation answers again, of
 * what each holds put through, comes to — the parts the part stands nowhere in included.
 *
 * <p>The second is written out here, as a walk of the statement as a tree that joins every one of
 * them again; the first hands back what it changed nothing in and meets a part shared by several
 * places once. The two are held to one spelling and one statement.
 *
 * <p>Drawn at random from a fixed seed: truths of a few positions, said to hold and not to, held
 * together and as alternatives, denied, read where another truth answers, counted, and said of
 * some element of a container — the same part met again in several places, and the same part
 * twice in one. The part put through is one of the truths, either way.
 */
class APartPutThroughAStatementComesToWhatJoiningItAgainWouldTest {

    private static final List<String> AT = List.of("a", "b", "c", "d");
    private static final DecisionSubject CONTAINER = new DecisionSubject.AnInput(
            TermPath.of("xs"));

    @Test
    void puttingAPartThroughComesToWhatJoiningAgainWould() {
        Random random = new Random(2937);
        for (int drawn = 0; drawn < 3000; drawn++) {
            List<Proposition> met = new ArrayList<>();
            Proposition stated = statement(random, 4, met, true);
            Proposition part = truth(random);
            boolean holds = random.nextBoolean();
            Proposition expected = joinedAgain(stated, part, holds);
            Proposition put = WhereEachLineDecides.with(stated, part, holds);
            String said = part.spelling() + " as " + holds + " through " + stated.spelling();
            assertEquals(expected.spelling(), put.spelling(), said);
            assertEquals(expected, put, said);
        }
    }

    /** What putting {@code part} through {@code stated} came to when every part was joined
     *  again: a walk of the statement as a tree. */
    private static Proposition joinedAgain(Proposition stated, Proposition part, boolean holds) {
        return switch (stated) {
            case Proposition.All all -> Proposition.all(all.parts().stream()
                    .map(each -> joinedAgain(each, part, holds)).toList());
            case Proposition.Any any -> Proposition.any(any.parts().stream()
                    .map(each -> joinedAgain(each, part, holds)).toList());
            case Proposition.WhereItAnswers where -> Proposition.whereItAnswers(
                    joinedAgain(where.answers(), part, holds),
                    joinedAgain(where.states(), part, holds));
            case Proposition.SoManyHold counted ->
                    counted.mapped(each -> joinedAgain(each, part, holds));
            case Proposition.OfTheWays ways -> joinedAgain(ways.written(), part, holds);
            case Proposition leaf when WhereEachLineDecides.standsAs(leaf, part) ->
                    new Proposition.Always(leaf.spelling().equals(part.spelling()) == holds);
            case Proposition.Some some when !part.mayTurnOnAnElementOf(some.container()) ->
                    new Proposition.Some(some.container(),
                            joinedAgain(some.ofTheElement(), part, holds), some.holds());
            default -> stated;
        };
    }

    /** A statement drawn at random, a part met before drawn again now and then; a quantifier
     *  or a statement read where an operation answers only where {@code mayQuantify}, which
     *  inside a quantifier it is not. */
    private static Proposition statement(Random random, int depth, List<Proposition> met,
                                         boolean mayQuantify) {
        if (!met.isEmpty() && random.nextInt(4) == 0) {
            return met.get(random.nextInt(met.size()));
        }
        int kind = random.nextInt(depth == 0 ? 1 : 7);
        Proposition out = switch (kind) {
            case 0 -> truth(random);
            case 1, 2 -> {
                List<Proposition> parts = new ArrayList<>();
                for (int at = 0; at < 2 + random.nextInt(3); at++) {
                    parts.add(statement(random, depth - 1, met, mayQuantify));
                }
                yield kind == 1 ? Proposition.all(parts) : Proposition.any(parts);
            }
            case 3 -> statement(random, depth - 1, met, mayQuantify).denied();
            // Read where an operation answers, which a quantifier does not hold.
            case 4 -> mayQuantify ? Proposition.whereItAnswers(truth(random),
                    statement(random, depth - 1, met, true)) : truth(random);
            case 5 -> counted(random);
            default -> mayQuantify
                    ? new Proposition.Some(CONTAINER, statement(random, depth - 1,
                            new ArrayList<>(), false), random.nextBoolean())
                    : truth(random);
        };
        met.add(out);
        return out;
    }

    private static Proposition truth(Random random) {
        return new Proposition.Truth(new DecisionSubject.AnInput(
                TermPath.of(AT.get(random.nextInt(AT.size())))), random.nextBoolean());
    }

    /** How many of two or three truths of different positions hold, one of them or more. */
    private static Proposition counted(Random random) {
        TreeMap<Spelling, Proposition> bySpelling = new TreeMap<>();
        for (int at = 0; at < 2 + random.nextInt(2); at++) {
            Proposition one = truth(random);
            bySpelling.put(one.spelling(), one);
        }
        if (bySpelling.size() < 2) {
            return truth(random);
        }
        List<Proposition> statements = List.copyOf(bySpelling.values());
        List<Integer> weights = statements.stream().map(_ -> 1).toList();
        return new Proposition.SoManyHold(statements, weights, List.of(1));
    }
}
