package souther.compiler.partition;

import java.util.List;
import java.util.Objects;

/**
 * What a row has to be, beside the way to a rule, to be evidence of one case a statement the rule
 * consults draws inside itself.
 *
 * <p>The way to the rule says the statement came out as the rule has it; this says what the case
 * adds about the node a search starts at. A row composed for the two together is a candidate for
 * the case, and whether it is evidence of it is for a run to say ({@link CasesTheRowsTook}) and
 * never for this: what is put on the way here is what the reading has words for.
 *
 * @param which the case
 * @param puts  what the case asks of the row, in the words the way to a rule is in
 * @param said  which copies of the model's code each entry was read off
 */
public record CaseWay(CaseOfAStatement which, List<OnTheWay> puts, SaidOnTheWay said) {

    public CaseWay {
        Objects.requireNonNull(which, "a way is to some case");
        Objects.requireNonNull(said, "what the entries were read off, or nothing");
        puts = List.copyOf(puts);
        if (puts.isEmpty()) {
            throw new IllegalArgumentException("a case that asks nothing of a row has no way: "
                    + which);
        }
    }
}
