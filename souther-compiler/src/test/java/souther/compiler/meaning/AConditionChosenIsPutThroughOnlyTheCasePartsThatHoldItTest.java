package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code CasesOfALineAsked.SoFar} puts a part chosen through the parts that hold it and no
 * others, so what it keeps is what putting every part through every other, as
 * {@link WhereEachLineDecides#given} does, would have kept. That is a claim about what
 * {@code given} leaves alone, and it is held here against the slow way: statements of every kind
 * a part can be, chosen in sequence, kept both ways, and the conjunctions compared after each.
 *
 * <p>Statements are made at random from a fixed seed, out of truths and comparisons, those over
 * an element of a container among them, and the conjunction, the disjunction, the statement read
 * where another answers, the quantifier over a container and the count of statements that hold
 * over them. The statement over the ways something is written out from is left out: it is made
 * from a reading of the model, which a statement written here is not.
 */
class AConditionChosenIsPutThroughOnlyTheCasePartsThatHoldItTest {

    private static final int SEQUENCES = 4000;

    private static final DecisionSubject CONTAINER =
            new DecisionSubject.AnInput(TermPath.of("items"));

    private static final List<DecisionSubject> SUBJECTS = List.of(
            new DecisionSubject.AnInput(TermPath.of("a")),
            new DecisionSubject.AnInput(TermPath.of("b")),
            new DecisionSubject.AnInput(TermPath.of("c")),
            new DecisionSubject.AnInput(TermPath.of("items").element()));

    /** What choosing {@code condition} after {@code chosen} keeps, every part put through every
     *  other: the part new put through those chosen, those chosen put through it. */
    private static List<Proposition> everyPartThroughEveryOther(List<Proposition> chosen,
                                                                Proposition condition) {
        List<Proposition> out = new ArrayList<>(chosen);
        for (Proposition part : condition instanceof Proposition.All all ? all.parts()
                : List.of(condition)) {
            Proposition left = part;
            for (Proposition each : out) {
                left = WhereEachLineDecides.given(left, each);
            }
            if (left instanceof Proposition.Always(boolean holds) && holds) {
                continue;
            }
            for (int at = 0; at < out.size(); at++) {
                out.set(at, WhereEachLineDecides.given(out.get(at), left));
            }
            out.add(left);
        }
        return out;
    }

    private static Proposition leaf(Random random) {
        DecisionSubject subject = SUBJECTS.get(random.nextInt(SUBJECTS.size()));
        Proposition one = random.nextInt(4) == 0
                ? atLeast(10 * random.nextInt(3)) : new Proposition.Truth(subject, true);
        return random.nextBoolean() ? one : one.denied();
    }

    /** The number {@code x} at or above {@code at}. */
    private static Proposition atLeast(int at) {
        Quantity x = new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("x")));
        Relation.OneWay<Quantity> one = Relation.OneWay.of(new LinearForm<>(ExactRatio.of(-at),
                new LinkedHashMap<>(Map.of(x, ExactRatio.ONE))), Rel.GE);
        return new Proposition.Compared(new Relation.Affine(one.form(), one.proposition()),
                one.holds());
    }

    /** A statement of some depth, made of the kinds a part can be; a leaf where one cannot be
     *  made of what was drawn. */
    private static Proposition statement(Random random, int depth) {
        if (depth == 0) {
            return leaf(random);
        }
        try {
            return switch (random.nextInt(7)) {
                case 0 -> Proposition.all(List.of(statement(random, depth - 1),
                        statement(random, depth - 1), statement(random, depth - 1)));
                case 1 -> Proposition.any(List.of(statement(random, depth - 1),
                        statement(random, depth - 1)));
                case 2 -> Proposition.whereItAnswers(statement(random, depth - 1),
                        statement(random, depth - 1));
                case 3 -> new Proposition.Some(CONTAINER, statement(random, depth - 1),
                        random.nextBoolean());
                case 4 -> {
                    List<Proposition> inside = new ArrayList<>(List.of(
                            statement(random, depth - 1), statement(random, depth - 1)));
                    inside.sort((one, other) -> one.spelling().compareTo(other.spelling()));
                    yield new Proposition.SoManyHold(inside, List.of(1, 1), List.of(1));
                }
                default -> leaf(random);
            };
        } catch (IllegalArgumentException cannotBeMade) {
            return leaf(random);
        }
    }

    @Test
    void whatIsKeptIsWhatEveryPartPutThroughEveryOtherKeeps() {
        Random random = new Random(3238);
        int changed = 0;
        int steps = 0;
        for (int sequence = 0; sequence < SEQUENCES; sequence++) {
            CasesOfALineAsked.SoFar fast = CasesOfALineAsked.SoFar.NOTHING;
            List<Proposition> slow = new ArrayList<>();
            List<Proposition> said = new ArrayList<>();
            for (int at = 0, most = 2 + random.nextInt(5); at < most; at++) {
                Proposition condition = statement(random, 1 + random.nextInt(3));
                said.add(condition);
                List<Proposition> before = List.copyOf(slow);
                fast = fast.and(condition);
                slow = everyPartThroughEveryOther(slow, condition);
                steps++;
                if (!slow.equals(concatenated(before, condition))) {
                    changed++;
                }
                assertEquals(Proposition.all(slow), fast.condition(),
                        () -> "chosen in this order: " + said);
            }
        }
        int changedInTheEnd = changed;
        int stepsInTheEnd = steps;
        assertTrue(changedInTheEnd > stepsInTheEnd / 10, () -> "a part was put through another in"
                + " only " + changedInTheEnd + " of " + stepsInTheEnd
                + " steps, which holds nothing of the claim");
    }

    /** What is kept where nothing is put through anything: each part of {@code condition} after
     *  {@code chosen}. */
    private static List<Proposition> concatenated(List<Proposition> chosen,
                                                  Proposition condition) {
        List<Proposition> out = new ArrayList<>(chosen);
        out.addAll(condition instanceof Proposition.All all ? all.parts() : List.of(condition));
        return out;
    }
}
