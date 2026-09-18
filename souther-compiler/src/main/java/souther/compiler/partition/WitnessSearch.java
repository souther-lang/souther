package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.regex.Meter;
import souther.compiler.values.ValueSet;

import java.util.function.Supplier;

/**
 * What a search composing a value at a position is given besides the region it runs inside.
 *
 * <p>Two things, and they are two because they answer different questions. {@link AdmittedValues} is
 * what the model leaves each position, which is a fact about the declarations; the allowance is how
 * much work looking for a value in one of those sets may take, which is a policy about this compiler.
 * Folded into one type, a set of values would own a budget — and then how much a search may spend
 * would travel as part of what the model admits, which is the shape #1577 kept out of {@link
 * souther.compiler.check.Carrier}.
 *
 * <p>Paired here rather than passed as two arguments so that neither arrives without the other. A
 * search handed a set and no allowance has to reach for one, and what it reaches for is a budget
 * nothing granted it.
 *
 * @param admitted what the declarations leave each position
 * @param allowance what one crossing of a set with a run may cost, asked per crossing. An allowance
 *                  shared between them would have the first question spend what the second needs,
 *                  and which of them went short would depend on the order they were asked in
 */
public record WitnessSearch(AdmittedValues admitted, Supplier<Meter> allowance) {

    public WitnessSearch {
        if (admitted == null || allowance == null) {
            throw new IllegalArgumentException(
                    "a value is composed out of what a position admits and within what looking for"
                            + " one may cost, and a search is given both or neither");
        }
    }

    /** A fresh allowance, for one crossing of a set with a run. */
    public Meter meter() {
        return allowance.get();
    }

    /**
     * What the declarations leave the values a place composed for {@code term} is one of.
     *
     * <p>Asked of the location the number is read from rather than of the number, because one
     * location is measured at as many numbers as the rules name of it and admits one set of values
     * — a rule about one of those numbers is what leaves the others short, which is the whole reason
     * the sets are here.
     *
     * <p><b>And every value there is where the number is one taken of the position rather than its
     * own.</b> {@code String.length(code)} counts a string and the place composed for it is a count;
     * the set holds the strings. Put to it, every count would be refused for not being one of them,
     * and a number of that kind would stop being offered a value at all.
     *
     * <p>Here and not at each search, because it is one rule about what the sets are keyed by.
     * Written out wherever a place is composed, a search added later reads the set of a location
     * against a count and refuses every value the position has.
     */
    private AdmittedValues.Admitted valuesAt(NumericTerm.FromOnePosition term) {
        return term instanceof NumericTerm.ValueOf ? admitted.at(term.position())
                : new AdmittedValues.Admitted.Values(ValueSet.ANY);
    }

    /**
     * The set to narrow a search by: what the declarations leave the position, or every value there
     * is where nothing worked one out.
     *
     * <p>For a search asked whether values exist that meet a question — never for one that writes
     * the value it finds into a row. What such a search answers is about the region, not about what
     * the declarations can be shown to admit, so a set nobody established is knowledge it does not
     * have rather than a set it may narrow by: narrowed by that, the question would be narrower
     * than what was established.
     *
     * <p>{@link ValueSet#ANY} here is the identity of the crossing and never an answer about what
     * the position admits.
     */
    public ValueSet toNarrowBy(NumericTerm.FromOnePosition term) {
        return valuesAt(term) instanceof AdmittedValues.Admitted.Values(ValueSet set)
                ? set : ValueSet.ANY;
    }

    /**
     * The set to compose a value out of, or null where nothing worked one out.
     *
     * <p>For a search whose answer is written into a row. A value composed out of a set nobody
     * established is a row offered at a position whose rules were never read, so there is nothing
     * to compose from and the search says so in the word it has for composing nothing.
     *
     * <p><b>The other answer to the same three states, and both are named here because the question
     * decides which.</b> Written at each search instead, one reading of the input composed a value
     * out of what nothing established while another beside it refused to — and which of the two a
     * position got depended on which reading reached it first.
     */
    public ValueSet toComposeFrom(NumericTerm.FromOnePosition term) {
        return valuesAt(term) instanceof AdmittedValues.Admitted.Values(ValueSet set) ? set : null;
    }
}
