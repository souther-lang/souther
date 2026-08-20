package souther.compiler.interaction;

import java.util.List;

/**
 * The decisions that determine one value together.
 *
 * <p>What a black-box combination measure has to assume about every pair of inputs, read instead. A
 * group is where two values each settled by a decision are consumed into one, so the answer is a
 * function of both and a row that leaves either of them at one outcome cannot tell what was done
 * with them.
 */
public record Interaction(List<Factor> factors) {

    public Interaction {
        factors = List.copyOf(factors);
    }

    @Override
    public String toString() {
        return factors.toString();
    }
}
