package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Whether a reading opened one way holds of a context is what the context assumes, asked without
 * writing every assumption out.
 *
 * <p>{@link StructuralContext#holds} answers from the case taken in at a sum and the containers
 * said to hold something; {@link StructuralContext#assumptions} is the whole account a reason reads.
 * The two are one statement, and this holds them to it over every opening of a small world: two
 * sums and a third no context names, both cases of each, and two containers and a third, in every
 * context those make.
 */
class WhetherAContextHoldsIsAnsweredByWhatItAssumesTest {

    private static final List<TermPath> SUMS =
            List.of(TermPath.of("a"), TermPath.of("b"), TermPath.of("c"));

    private static final List<TermPath> CONTAINERS =
            List.of(TermPath.of("xs"), TermPath.of("ys"), TermPath.of("zs"));

    private static final List<Refinement> CASES = List.of(
            Refinement.of(new Case.Presence(true)), Refinement.of(new Case.Presence(false)));

    @Test
    void holdsSaysWhatTheAssumptionsSay() {
        int asked = 0;
        for (StructuralContext context : contexts()) {
            for (RootOpening opening : openings()) {
                assertEquals(assumed(context, opening), context.holds(opening),
                        () -> opening + " under " + context.assumptions());
                asked++;
            }
        }
        assertEquals(contexts().size() * openings().size(), asked);
    }

    /** What the context's whole account says of {@code opening}. */
    private static boolean assumed(StructuralContext context, RootOpening opening) {
        return switch (opening) {
            case RootOpening.Taken _ -> true;
            case RootOpening.Refined it -> context.assumptions().contains(
                    new StructuralContext.Assumption.TheCaseAt(it.crossing().sum(),
                            CasesLeft.of(it.crossing().branch())));
            case RootOpening.Inside it -> context.assumptions().contains(
                    new StructuralContext.Assumption.HoldingSomething(it.container()));
        };
    }

    /** No case, one case at one sum, and a case at each of two, beside every split of two
     *  containers into holding something, holding none, and neither. */
    private static List<StructuralContext> contexts() {
        List<Requirements> refined = new ArrayList<>(List.of(Requirements.NONE));
        for (Refinement one : CASES) {
            refined.add(Requirements.NONE.and(SUMS.get(0), one));
            for (Refinement other : CASES) {
                refined.add(Requirements.NONE.and(SUMS.get(0), one).and(SUMS.get(1), other));
            }
        }
        List<List<Set<TermPath>>> splits = List.of(
                List.of(Set.of(), Set.of()),
                List.of(Set.of(CONTAINERS.get(0)), Set.of()),
                List.of(Set.of(), Set.of(CONTAINERS.get(0))),
                List.of(Set.of(CONTAINERS.get(0)), Set.of(CONTAINERS.get(1))),
                List.of(Set.of(CONTAINERS.get(0), CONTAINERS.get(1)), Set.of()));
        List<StructuralContext> out = new ArrayList<>();
        for (Requirements each : refined) {
            for (List<Set<TermPath>> split : splits) {
                out.add(new StructuralContext(each, split.get(0), split.get(1)));
            }
        }
        return out;
    }

    /** Every way a reading opens over the world: taken, under each case of each sum, and inside
     *  each container. */
    private static List<RootOpening> openings() {
        List<RootOpening> out = new ArrayList<>(List.of(new RootOpening.Taken()));
        for (TermPath sum : SUMS) {
            for (Refinement branch : CASES) {
                out.add(new RootOpening.Refined(TermPath.of("r"),
                        new SharedNames(sum, branch, Set.of())));
            }
        }
        for (TermPath container : CONTAINERS) {
            out.add(new RootOpening.Inside(TermPath.of("r"), container));
        }
        return out;
    }
}
