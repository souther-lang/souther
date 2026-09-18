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
     * is where the reading answered for no position at that path.
     *
     * <p>For a search asked whether values exist that meet a question — never for one that writes
     * the value it finds into a row. What such a search answers is about the region, not about what
     * the declarations can be shown to admit, so a set nobody established is knowledge it does not
     * have rather than a set it may narrow by: narrowed by that, the question would be narrower
     * than what was established.
     *
     * <p>One answer for the two states that hold no set, and this is the question where they come
     * to the same thing: neither narrows anything, so a reading that stopped and a path the values
     * stand below are both the identity of the crossing here. What tells them apart is what may be
     * written ({@link #toComposeFrom}).
     *
     * <p>{@link ValueSet#ANY} here is the identity of the crossing and never an answer about what
     * the position admits.
     */
    public ValueSet toNarrowBy(NumericTerm.FromOnePosition term) {
        return switch (valuesAt(term)) {
            case AdmittedValues.Admitted.Values(ValueSet set) -> set;
            case AdmittedValues.Admitted.NotWorkedOut _,
                 AdmittedValues.Admitted.StandsUnderTheCases _ -> ValueSet.ANY;
        };
    }

    /**
     * What a search whose answer is written into a row composes a value out of.
     *
     * <p><b>The other answer to the same three states, and both are named here because the question
     * decides which.</b> Written at each search instead, one reading of the input composed a value
     * out of what nothing established while another beside it refused to — and which of the two a
     * position got depended on which reading reached it first.
     *
     * <p>Three answers and not a set or nothing, because this is the question the three states come
     * apart on. A set nobody established composes nothing: a row offered at a position whose rules
     * were never read is one this compiler cannot stand behind. A path the reading puts no position
     * at composes from the run alone, and what becomes of the row is the construction's to say.
     */
    public ComposingFrom toComposeFrom(NumericTerm.FromOnePosition term) {
        return switch (valuesAt(term)) {
            case AdmittedValues.Admitted.Values(ValueSet set) ->
                    new ComposingFrom.TheSetThePositionAdmits(set);
            case AdmittedValues.Admitted.NotWorkedOut _ -> new ComposingFrom.NothingWorkedItOut();
            case AdmittedValues.Admitted.StandsUnderTheCases _ -> new ComposingFrom.TheRunAlone();
        };
    }

    /**
     * What a value written into a row at one position is composed out of.
     *
     * <p>The action beside the fact, and a type of its own because the two are not the same answer.
     * What a position admits is what the declarations left it ({@link AdmittedValues.Admitted}); this
     * is what a search may put a value together from, which the question decides — and two of these
     * cross the run with the same set while saying unlike things about the model.
     *
     * <p>Which set that is is read here and at no search, so that a search added later does not
     * decide it again ({@link #toCrossTheRunWith}).
     */
    public sealed interface ComposingFrom {

        /**
         * The set to cross the run with, or null where nothing composes a value here.
         *
         * <p>Declared rather than switched over, so that a state added to this is a state whose
         * answer somebody writes. Matched on instead, a new one would be composed out of whatever
         * the condition beside it happened to leave it with.
         */
        ValueSet toCrossTheRunWith();

        /** What the declarations leave the position, which a value written there is one of. */
        record TheSetThePositionAdmits(ValueSet set) implements ComposingFrom {

            public TheSetThePositionAdmits {
                if (set == null) {
                    throw new IllegalArgumentException(
                            "a position whose set was read composes from it, and one whose set was"
                                    + " not composes from nothing rather than from null");
                }
            }

            @Override
            public ValueSet toCrossTheRunWith() {
                return set;
            }
        }

        /**
         * The run, with nothing of this reading's narrowing it, because the path is no position of
         * this reading and the value stands below it.
         *
         * <p>{@link ValueSet#ANY} is the identity of the crossing here and no answer about what any
         * position admits. There are no rules of this path to have read — a name the cases of a sum
         * share is written above the values answering it — so a value is offered and whatever writes
         * the row says whether it can be written.
         */
        record TheRunAlone() implements ComposingFrom {

            @Override
            public ValueSet toCrossTheRunWith() {
                return ValueSet.ANY;
            }
        }

        /**
         * Nothing, because nothing worked out what the position holds.
         *
         * <p>A row composed here would be offered at a position whose rules this compiler never
         * read, so the search comes back in the word it has for composing nothing rather than
         * offering a value against a set nobody established.
         */
        record NothingWorkedItOut() implements ComposingFrom {

            @Override
            public ValueSet toCrossTheRunWith() {
                return null;
            }
        }
    }
}
