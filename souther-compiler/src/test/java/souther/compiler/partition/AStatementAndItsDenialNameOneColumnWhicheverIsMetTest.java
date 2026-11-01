package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.Spelling;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Random;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A statement met coming out one way and its denial met coming out the other are one column with
 * one answer, whichever of them is met, and so is a statement its denial denies back to, spelled
 * another way ({@link DecisionCondition.AStatement#of}).
 *
 * <p>Joining is no normal form, so the denial of a denial may be a second spelling of the
 * statement; named by either, a column would be two columns, and named by the denial where the
 * denial's own denial spells first, refused as its own denial's.
 *
 * <p>Drawn at random from a fixed seed, as
 * {@code DenyingAStatementOverAndOverComesRoundToTwoThatDenyOneAnotherTest} draws them: truths and comparisons, held together and as alternatives, denied, read where a
 * truth answers, counted, said of some element of a container, and a condition beside each way of
 * it as joining an if writes it.
 */
class AStatementAndItsDenialNameOneColumnWhicheverIsMetTest {

    private static final List<String> AT = List.of("a", "b", "c");
    private static final DecisionSubject CONTAINER = new DecisionSubject.AnInput(
            TermPath.of("xs"));

    @Test
    void aStatementAndEveryDenialOfItAreOneColumnWithOneAnswer() {
        Random random = new Random(2937);
        for (int drawn = 0; drawn < 3000; drawn++) {
            Proposition stated = statement(random, 4, true);
            Proposition once = stated.denied();
            Proposition twice = once.denied();
            Optional<DecidedCondition.Held> holding = DecisionCondition.AStatement.of(once, true);
            assertTrue(holding.isPresent(), stated::toString);
            assertEquals(holding, DecisionCondition.AStatement.of(twice, false),
                    stated::toString);
            assertEquals(holding, DecisionCondition.AStatement.of(twice.denied(), true),
                    stated::toString);
        }
    }

    private static Proposition statement(Random random, int depth, boolean mayQuantify) {
        int kind = random.nextInt(depth == 0 ? 2 : 8);
        return switch (kind) {
            case 0 -> truth(random);
            case 1 -> comparison(random);
            case 2, 3 -> {
                List<Proposition> parts = new ArrayList<>();
                for (int at = 0; at < 2 + random.nextInt(3); at++) {
                    parts.add(statement(random, depth - 1, mayQuantify));
                }
                yield kind == 2 ? Proposition.all(parts) : Proposition.any(parts);
            }
            case 4 -> statement(random, depth - 1, mayQuantify).denied();
            case 5 -> {
                Proposition condition = truth(random);
                yield Proposition.any(List.of(
                        Proposition.all(List.of(condition,
                                statement(random, depth - 1, mayQuantify))),
                        Proposition.all(List.of(condition.denied(),
                                statement(random, depth - 1, mayQuantify)))));
            }
            case 6 -> mayQuantify ? Proposition.whereItAnswers(truth(random),
                    statement(random, depth - 1, true)) : counted(random);
            default -> mayQuantify
                    ? new Proposition.Some(CONTAINER,
                            statement(random, depth - 1, false), random.nextBoolean())
                    : counted(random);
        };
    }

    private static Proposition truth(Random random) {
        return new Proposition.Truth(new DecisionSubject.AnInput(
                TermPath.of(AT.get(random.nextInt(AT.size())))), random.nextBoolean());
    }

    private static Proposition comparison(Random random) {
        DecisionAtom at = new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("n")));
        Relation.OneWay<Quantity> one = Relation.OneWay.of(
                new LinearForm<>(ExactRatio.of(random.nextInt(5) - 2), Map.of(at, ExactRatio.ONE)),
                new Rel[] {Rel.GE, Rel.GT, Rel.EQ}[random.nextInt(3)]);
        return new Proposition.Compared(new Relation.Affine(one.form(), one.proposition()),
                one.holds() == random.nextBoolean());
    }

    private static Proposition counted(Random random) {
        TreeMap<Spelling, Proposition> bySpelling = new TreeMap<>();
        for (int at = 0; at < 3; at++) {
            Proposition one = truth(random);
            bySpelling.put(one.spelling(), one);
        }
        if (bySpelling.size() < 2) {
            return truth(random);
        }
        List<Proposition> statements = List.copyOf(bySpelling.values());
        return new Proposition.SoManyHold(statements, statements.stream().map(_ -> 1).toList(),
                List.of(1));
    }
}
