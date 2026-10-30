package souther.compiler.partition;

import souther.compiler.observe.RunSensitivity;

/**
 * A population this compiler offers some of rather than all of.
 *
 * <p><b>Apart from {@link CompositionBudget}, and the difference is what a reader can do.</b> A
 * figure is a number somebody wrote down: raise it and the search goes on to what it was holding.
 * One of these is a set of values this compiler has no way of producing the rest of — raising
 * anything reaches none of them, and what would is somebody writing the rest. Held in one
 * vocabulary, the two are a set a reader unions and then acts on by raising a number that changes
 * nothing.
 *
 * <p>So neither is the other's default. A walk under a figure that ran out of pieces reached no
 * figure at all, and a walk that went everywhere it knows how to go refused nothing — and both
 * leave an offer that is not the whole of what there is, which is the one thing they have in
 * common and the reason both have to travel.
 *
 * <p><b>Said only where it cannot be shown otherwise.</b> A walk that produced everything of its
 * kind says so, and every other walk is one of these: an offer claiming to be everything is a claim
 * about a population, and the walk that would have to have enumerated it is the only thing that
 * could establish one. So this is what a walk says by default, and completeness is what it has to
 * prove.
 */
public enum CompositionRepertoire {

    /**
     * The ways a difference is spread over the elements of a container adding up to a total.
     *
     * <p>Two are written — the whole of it on as few elements as will carry it, and as near an
     * equal share each as the order allows — and the arrangements of more than one element are
     * many. Which of them a rule tells apart is the rule's own business, so no reading of the two
     * says anything about the rest.
     *
     * <p>Elements the total leaves out — those at positions a total of some of them does not take —
     * are written at one value each, which is one of the values they could hold.
     */
    WAYS_A_TOTAL_IS_SPREAD,

    /**
     * The places on a line between two positions that a pair is tried standing at.
     *
     * <p>Where the order has a smallest step, the places either side of the first one are stepped
     * to and what stops the walk is a figure ({@link CompositionBudget#PLACES_A_PAIR_IS_TRIED_AT}).
     * Where it has none there is no step to take, so the one place the two ranges give up is the
     * whole of what this names — and the line holds every other place it could have named. Raising
     * anything reaches none of them; what would is a way of naming a second place on such an order.
     *
     * <p>Which is why a pair found nowhere there is this and not a proof. Two strings the rules
     * leave a pair for anywhere but at that one place come back with nothing composed, and read as
     * an answer about the rules it says the model refuses a relation it satisfies.
     */
    PLACES_A_PAIR_IS_TRIED_AT_ON_A_LINE,

    /**
     * The values that answer several of their own numbers at once.
     *
     * <p>A location asked for two numbers is one value to write, and how a value with both is come
     * by depends on how its numbers are reached: a number that is a place in the spelling of what
     * stands there is written at, one whose values come of a run of the place's own is solved for,
     * and one read off a value the group already asks for is read off the values that demand
     * admits, and one it is composed out of is composed for. Which groups those are is the
     * realizer's to say and is not spelled out here; what this names is the values left over, whose
     * numbers are reached none of those ways. Totals of the fields of their own of one container's
     * elements are composed together, one share of each for each element; what is left over is
     * totals that read one field, a total computed of several fields beside another, and a choice
     * among forms of a field solved for beside another total.
     *
     * <p>So a group nothing built a value for is not a group no value answers. Raising anything
     * reaches none of them; what would is somebody writing the solving.
     */
    VALUES_THAT_ANSWER_SEVERAL_OF_THEIR_NUMBERS,

    /**
     * The places inside one run of an order that this compiler names a value at.
     *
     * <p>It names one. Where the order has a smallest step there are others to step to and nothing
     * here steps to them; where it has none — a decimal, a moment — there is no step to take at
     * all, and the one place the run gives up is the whole of what this compiler can name in it.
     * Raising anything reaches none of the rest, which is what makes this a population and not a
     * figure: what would reach them is a way of naming a second place in a run.
     *
     * <p>So a class whose one named place builds nothing is not a class with no value in it. Read
     * as a figure, an author is told to raise a number that changes nothing; read as an answer
     * about the model, they are told the range holds no value when what happened is that this
     * compiler tried one of them.
     */
    PLACES_IN_A_RUN_THAT_ARE_NAMED,

    /**
     * The elements chosen for how many of a container's elements meet a statement.
     *
     * <p>Chosen where the element is one number the statement reads, against numbers beside it that
     * stand at one value. An element holding the number inside it, or two numbers, or a statement
     * read over the elements of another container, is chosen by nothing here: what would reach it
     * is a way of choosing such elements, and raising no figure does.
     */
    ELEMENTS_CHOSEN_FOR_A_COUNT,

    /**
     * The keys placed beside the number their own elements come to, where the key is a field that
     * number is made of.
     *
     * <p>The key is another parameter's and is fixed before the elements are composed, while the
     * elements of a key come to a number that turns on the key. Where each element adds the key
     * itself, the key is placed at the number asked for and a row holds one element of it; a key
     * that divides the number, with that many elements, is one of the others, and so is a size
     * of the container that asks for more elements than one. Where the number is made of the
     * key and something more, the key is a value the rules leave and nothing relates it to the
     * number. All of them are written by none of these. Raising no figure reaches them; what
     * would is a way of choosing the key and the elements of it together.
     */
    KEYS_PLACED_AT_THE_NUMBER_THEIR_ELEMENTS_COME_TO,

    /**
     * The keys of one fold asked for together, at the values and with the numbers this tries.
     *
     * <p>Each key is another parameter's and is fixed before the elements are composed. Two keys
     * are held at different values where they can be, and a key only counted — asked how many
     * elements have it, with no number asked of them — is written to come to the number the first
     * total of the group asks, since the composer of counts stops at a figure of its own where the
     * elements are the fields of a record. A key counted beside a number it need not come to, and
     * a count that asks more of a key than that number allows, are written by none of these.
     * Raising no figure reaches them; what would is a way of choosing the keys and the elements
     * of each together.
     */
    KEYS_OF_ONE_FOLD_ASKED_TOGETHER,

    /**
     * The elements of a key whose least or greatest value is asked for, written as one element.
     *
     * <p>One element is its own least and its own greatest, so an end is written as one. A
     * container that must hold more of that key's elements — its type holds two, or a count of the
     * key's elements asks for more than one — has the end among several, and so does a key whose
     * end is not any one element's number; they are written by none of these. Raising no figure
     * reaches them; what would is a way of writing the end with the other elements of the key
     * around it.
     */
    ENDS_OF_A_KEY_WRITTEN_AS_ONE_ELEMENT,

    /**
     * The totals of a key from the last of its elements that puts its number in place of the
     * ones before, among the elements adding up to them.
     *
     * <p>One element is a key whose total is its own number, whichever case it is of, so such a
     * total is written as one. A container that must hold more of that key's elements, and a
     * total no one element's number comes to, are written by none of these; what would is a way
     * of writing the elements after the last put so that they add up to it.
     */
    TOTALS_FROM_A_PUT_WRITTEN_AS_ONE_ELEMENT,

    /**
     * The elements whose computed number is made of the fields of one element in ways this
     * compiler solves for.
     *
     * <p>A total of what a walk computed of each element is written by choosing one field of every
     * element and solving for it, where the computation is a form of that one field once the
     * others it reads are held still. A choice between two by a flag has two numbers to choose
     * between in an element, and nothing here chooses which. A choice by the element's case none of
     * whose arms is a form of one field of its case is the same, and so is a weight made of the
     * position or a choice by it between two forms of the field, which weigh the positions apart.
     * Raising anything reaches none of them; what would is a way of choosing the rest of an
     * element.
     *
     * <p>So a total of such a number is not a total no row comes to. Read as a figure, an author is
     * told to raise a number that changes nothing; read as an answer about the model, they are told
     * the rules admit no row when what happened is that this compiler wrote none.
     */
    ELEMENTS_A_COMPUTED_TOTAL_IS_SOLVED_FOR,

    /**
     * The containers a total of what was computed of each element is spread over, where the
     * elements differ at a field the computation reads besides the one solved for.
     *
     * <p>A computation of several fields, a form of them or their products, is solved for one field
     * with every other one it reads held at one value, the same in every element. A container whose
     * elements hold different values there comes to totals none of these do — a product of two
     * fields held at one is the other field's total, and every other total of products is written
     * by none of these. What would reach them is a way of sharing a total out over several fields,
     * and raising no figure does.
     */
    ELEMENTS_WITH_THE_OTHER_FIELDS_HELD_STILL,

    /**
     * The containers a total of what was computed of each element by its case is spread over,
     * where they mix the cases.
     *
     * <p>Such a total is solved for through one arm, which is a form of one field of the case it
     * takes, so every element written is of that case. A container mixing it with another case
     * comes to a total no container of one case does — twice an amount is even, and an odd fee
     * beside it is not — and is written by none of these. What would reach it is a way of sharing a
     * total out among the arms, and raising no figure does.
     */
    MIXES_OF_CASES_A_TOTAL_IS_SPREAD_OVER,

    /**
     * The trees written for how many nodes, or values inside the nodes, a tree holds.
     *
     * <p>Written as a root and nodes below it holding nothing below them. A tree of that many
     * nodes is one of those wherever a node may hold as many below it as the count leaves; where
     * the rules hold how many a node holds below it to fewer — one each, a chain — a tree of that
     * many is deeper, and none of these. A count of values inside the nodes is written by none of
     * them. Neither is a count no tree comes to: what would reach it is a way of writing deeper
     * trees, and raising no figure does.
     */
    TREES_WRITTEN_FOR_A_COUNT,

    /**
     * The trees written for how long the line is that a search down them finds: from the root to
     * the first node, in the order the search goes down, that holds the value it is for.
     *
     * <p>Written as a chain: each node the only element below the one above it, the last holding
     * the value the search is for at one field and the nodes above it holding another value there,
     * as many nodes as the line asked for. A line past those is not written — a value held at a
     * field of a field of the node, nodes below a node that are not a list, a value searched for
     * that stands at no one value — and none of it is a line no tree makes: what would reach it
     * is a way of writing the nodes, and raising no figure does.
     */
    TREES_WRITTEN_FOR_A_LINE,

    /**
     * The strings written for how many code points of a class what a case conversion makes of them
     * holds.
     *
     * <p>A string is written out of the code points of the class itself, and offered where the
     * run time's answer holds the count asked for. A string whose answer holds it by other code
     * points — the capitals a lowercase counts as letters, a digit where the plain letters are
     * tried first, a letter composed with a mark after it — is found by none of them. Neither is
     * a count no string comes to: what would reach it is a way of writing strings backwards through
     * the conversion, and raising no figure does.
     */
    STRINGS_A_CASE_CONVERSION_IS_WRITTEN_FOR,

    /**
     * The maps whose values come to a total, written with the one entry that holds it. A map of
     * several entries coming to the same total, and a map whose entries are asked to hold
     * something beside the number, are written by no way here; raising no figure does, and a total
     * only such a map comes to is not one no map comes to.
     */
    MAPS_WRITTEN_WITH_ONE_ENTRY,

    /**
     * The rows whose run works a number out at an item, for a number only a run works out.
     *
     * <p>Nothing says where the input's numbers stand for the run to come to a value there, so a
     * row is looked for by writing candidates and running each. The candidates are rows of a few
     * sizes and values; a row the item asks for elsewhere — a longer list, a value no candidate
     * holds — is found by none of them, and that none was found is not that none is there. What
     * would reach the rest is a way of writing the candidates the run turns on, and raising no
     * figure does.
     */
    ROWS_A_RUN_IS_TRIED_FOR;

    /**
     * Whether a row that meets this for one value of a point meets it for every other: the
     * population is of the number and not of the value it was asked at.
     *
     * <p>A computed total with no field to solve for is one, since which way solves it is read off
     * the computation and never off the total asked for, so a second value is written by nothing
     * the first was not. The others are walks of what one value admits — the ways it is spread,
     * the places a pair stands, the elements chosen — and another value admits others.
     */
    public boolean metWhateverTheValue() {
        return switch (this) {
            case ELEMENTS_A_COMPUTED_TOTAL_IS_SOLVED_FOR -> true;
            case WAYS_A_TOTAL_IS_SPREAD, PLACES_A_PAIR_IS_TRIED_AT_ON_A_LINE,
                 VALUES_THAT_ANSWER_SEVERAL_OF_THEIR_NUMBERS, PLACES_IN_A_RUN_THAT_ARE_NAMED,
                 ELEMENTS_CHOSEN_FOR_A_COUNT, KEYS_PLACED_AT_THE_NUMBER_THEIR_ELEMENTS_COME_TO,
                 KEYS_OF_ONE_FOLD_ASKED_TOGETHER, ENDS_OF_A_KEY_WRITTEN_AS_ONE_ELEMENT,
                 TOTALS_FROM_A_PUT_WRITTEN_AS_ONE_ELEMENT,
                 MIXES_OF_CASES_A_TOTAL_IS_SPREAD_OVER, ELEMENTS_WITH_THE_OTHER_FIELDS_HELD_STILL,
                 TREES_WRITTEN_FOR_A_COUNT, TREES_WRITTEN_FOR_A_LINE,
                 STRINGS_A_CASE_CONVERSION_IS_WRITTEN_FOR,
                 MAPS_WRITTEN_WITH_ONE_ENTRY, ROWS_A_RUN_IS_TRIED_FOR -> false;
        };
    }

    /**
     * Whether a wider run could reach the rest: never, since raising anything reaches none of it.
     * What would is somebody writing the rest, which is no run of this compiler.
     */
    public RunSensitivity runSensitivity() {
        return RunSensitivity.UNAFFECTED;
    }
}
