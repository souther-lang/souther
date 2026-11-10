package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.abort.AbortKind;
import souther.compiler.abort.AbortSet;
import souther.compiler.abort.GetsPast;
import souther.compiler.check.WhatARunMayEndFor.Endings;
import souther.compiler.core.KernelContracts;
import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawSubject;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ValueName;

import java.util.function.UnaryOperator;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an operation the library writes in the language ends a run for is what its body ends one
 * for, read off the body of the library it is asked of: the same operation written another way
 * answers what the other body does, under the same name and signature.
 */
class WhatAnOperationTheLibraryWritesEndsARunForTest {

    private static final ValueName.Stdlib.Operation IS_EMPTY =
            ValueName.Stdlib.operation("List", "isEmpty");
    private static final ValueName.Stdlib.Operation APPEND =
            ValueName.Stdlib.operation("List", "append");
    private static final ValueName.Stdlib.Operation ANY =
            ValueName.Stdlib.operation("List", "any");
    private static final ValueName.Stdlib.Operation LENGTH =
            ValueName.Stdlib.operation("List", "length");
    private static final ValueName.Stdlib.Operation FILTER_MAP =
            ValueName.Stdlib.operation("List", "filterMap");

    private static final String IS_EMPTY_BODY = "List.length(xs) == 0";
    private static final String APPEND_BODY = "= a ++ b";
    private static final String ANY_BODY = "List.fold((acc, x) -> acc || p(x), false, xs)";

    private static final Endings NONE = new Endings.Known(AbortSet.NONE);

    /** Control: as shipped, {@code List.isEmpty} is a comparison of a length, which ends no run. */
    @Test
    void anOperationWhoseBodyEndsNoRunEndsNone() {
        assertEquals(NONE, LibraryEndings.shipped().of(IS_EMPTY));
    }

    /** The same name and signature over a body joining two lists ends a run where the join does. */
    @Test
    void whatTheBodyEndsARunForIsWhatTheOperationDoes() {
        Stdlib rewritten = rewritten(IS_EMPTY_BODY, "List.length(xs ++ xs) == 0");

        assertEquals(new Endings.Known(AbortSet.of(AbortKind.REQUIRED_FORM_HAS_NO_PLACE)),
                LibraryEndings.of(rewritten).of(IS_EMPTY));
    }

    /** A quotient builds nothing, and ends a run for a divisor of nought only where its divisor
     *  may be nought where it is worked out. */
    @Test
    void aQuotientEndsARunForWhatItsSitesDo() {
        assertEquals(new Endings.Known(AbortSet.of(AbortKind.REQUIRED_FORM_HAS_NO_PLACE)),
                endingsOfIsEmptyAs("List.length(xs) / 1 >= 0"));
        assertEquals(new Endings.Known(AbortSet.of(AbortKind.DIVISION_BY_ZERO,
                        AbortKind.REQUIRED_FORM_HAS_NO_PLACE)),
                endingsOfIsEmptyAs("1 / List.length(xs) >= 0"));
    }

    /**
     * A site is asked where the body reaches it: the right of {@code &&} only past a left that
     * held, the right of {@code ||} only past one that did not, an arm only where the fork takes
     * it. One reached on no way ends nothing; a quotient reached only where its divisor is not
     * nought ends nothing for it, and a whole number reached only where it stays inside an
     * {@code Int} nothing for passing it. Each is beside the same site reached where what it ends
     * a run for may happen.
     */
    @Test
    void aSiteEndsARunOnlyWhereTheBodyReachesIt() {
        Endings quotient = endingsOfIsEmptyAs("1 / List.length(xs) >= 0");
        Endings passing = new Endings.Known(AbortSet.of(AbortKind.REQUIRED_FORM_HAS_NO_PLACE));
        for (String never : new String[] {"false && 1 / List.length(xs) >= 0",
                "true || 1 / List.length(xs) >= 0"}) {
            assertEquals(NONE, endingsOfIsEmptyAs(never), never);
        }
        for (String spared : new String[] {"List.length(xs) > 0 && 1 / List.length(xs) >= 0",
                "List.length(xs) == 0 || 1 / List.length(xs) >= 0",
                "if List.length(xs) == 0 then true else 1 / List.length(xs) >= 0"}) {
            assertEquals(passing, endingsOfIsEmptyAs(spared), spared);
        }
        for (String reached : new String[] {"List.length(xs) == 0 && 1 / List.length(xs) >= 0",
                "List.length(xs) > 0 || 1 / List.length(xs) >= 0",
                "if List.length(xs) > 0 then true else 1 / List.length(xs) >= 0"}) {
            assertEquals(quotient, endingsOfIsEmptyAs(reached), reached);
        }
        assertEquals(NONE, endingsOfIsEmptyAs(
                "List.length(xs) < 10 && List.length(xs) + 9223372036854775790 > 0"));
        assertEquals(passing, endingsOfIsEmptyAs(
                "List.length(xs) > 10 && List.length(xs) + 9223372036854775790 > 0"));
    }

    /**
     * A site under a closure runs wherever the closure is applied, and the proofs see only the
     * applications they make: a closure handed to an operation read by its law, or let-bound and
     * handed to the walk, runs on values no reading of the body meets. Applied once more where no
     * run goes, its site is not read as reached on no way, nor its quotient as never by nought.
     */
    @Test
    void aSiteUnderAClosureRunOnValuesTheProofsDoNotSeeEndsWhatItMay() {
        String f = "{\n    let f = n -> 100 / n\n    ";
        for (String body : new String[] {
                f + "if false then f(1) >= 0 else List.length(List.map(f, [List.length(xs)])) == 0\n}",
                f + "if List.length(xs) > 0 then f(List.length(xs)) >= 0"
                        + " else List.length(List.map(f, [List.length(xs)])) == 0\n}",
                f + "if false then f(1) >= 0"
                        + " else List.fold((acc, n) -> acc && f(n) > 0, true, [List.length(xs)])\n}",
                "{\n    let step = (acc, n) -> acc && 100 / n > 0\n    if false then step(true, 1)"
                        + " else List.fold(step, true, [List.length(xs)])\n}"}) {
            assertTrue(((Endings.Known) endingsOfIsEmptyAs(body)).kinds()
                    .contains(AbortKind.DIVISION_BY_ZERO), body);
        }
    }

    /** A join is of the type of its two sides, so the empty list on one side says nothing of what
     *  the other holds: what is worked out of its elements is read at their type all the same. */
    @Test
    void aJoinWithTheEmptyListIsOfWhatTheOtherSideHolds() {
        String walk = "List.fold((acc, n) -> acc && n + 9223372036854775800 > 0, true, %s)";
        assertEquals(endingsOfIsEmptyAs(walk.formatted("[List.length(xs)]")),
                endingsOfIsEmptyAs(walk.formatted("[] ++ [List.length(xs)]")));
        assertEquals(new Endings.Known(AbortSet.of(AbortKind.REQUIRED_FORM_HAS_NO_PLACE)),
                endingsOfIsEmptyAs(walk.formatted("[List.length(xs)]")));
    }

    private static Endings endingsOfIsEmptyAs(String body) {
        return LibraryEndings.of(rewritten(IS_EMPTY_BODY, body)).of(IS_EMPTY);
    }

    private static final ValueName.Stdlib.Operation ABS = ValueName.Stdlib.operation("Decimal", "abs");

    private static final String ABS_BODY = "if d < 0.0m then 0.0m - d else d";

    private static GetsPast completionOfAbsAs(String body) {
        return LibraryEndings.of(rewritten(ABS_BODY, body)).completionApartFromWhatItIsHanded(ABS);
    }

    /**
     * A body that works decimals out asks the room of each operation it does, over what the call
     * is handed and what is written, and answers at the scale its parts do: the shipped {@code abs}
     * takes a number from a written nought, and the same body over a product asks the product's
     * room as well. One whose operand is no number the arguments and what is written decide is not
     * known.
     */
    @Test
    void aBodyWorkingDecimalsOutAsksTheRoomOfEachOperation() {
        assertEquals(1, roomsOf(LibraryEndings.shipped().completionApartFromWhatItIsHanded(ABS)));
        assertEquals(2, roomsOf(completionOfAbsAs("if d < 0.0m then 0.0m - d else d * d")));
        assertEquals(new GetsPast.NotKnown(),
                completionOfAbsAs("if d < 0.0m then 0.0m - Decimal.round(2, HALF_UP, d) else d"));
    }

    private static int roomsOf(GetsPast completion) {
        assertTrue(completion instanceof GetsPast.WhereTheScalesHaveRoom, completion.toString());
        return ((GetsPast.WhereTheScalesHaveRoom) completion).rooms().size();
    }

    /** A kernel's is what its contract says, and not read again here. */
    @Test
    void aKernelEndsARunForWhatItsContractSays() {
        Stdlib library = DefaultStdlib.get();

        assertEquals(new Endings.Known(KernelContracts.abortsOf(
                        library.intrinsicOf(LENGTH).kernel())),
                LibraryEndings.of(library).of(LENGTH));
    }

    /** An operation coming back to itself is not known until the cycle is read. */
    @Test
    void anOperationCallingItselfIsNotKnown() {
        Stdlib rewritten = rewritten(IS_EMPTY_BODY,
                "if List.length(xs) == 0 then true else List.isEmpty([])");

        assertEquals(new Endings.NotKnown(), LibraryEndings.of(rewritten).of(IS_EMPTY));
    }

    /** Nor is one coming back to itself through another, nor the other. */
    @Test
    void twoOperationsCallingEachOtherAreNotKnown() {
        Stdlib rewritten = rewritten(text -> text
                .replace(IS_EMPTY_BODY, "List.length(List.append(xs, [])) == 0")
                .replace(APPEND_BODY, "= if List.isEmpty(a) then b else a ++ b"));
        LibraryEndings endings = LibraryEndings.of(rewritten);

        assertEquals(new Endings.NotKnown(), endings.of(IS_EMPTY));
        assertEquals(new Endings.NotKnown(), endings.of(APPEND));
    }

    /** A function it is handed is the caller's, so what applying it ends a run for is not known. */
    @Test
    void applyingAFunctionItIsHandedIsNotKnown() {
        Stdlib rewritten = rewritten(ANY_BODY,
                "match List.get(0, xs) with\n        | Some x -> p(x)\n        | None -> false");

        assertEquals(new Endings.NotKnown(), LibraryEndings.of(rewritten).of(ANY));
    }

    /**
     * A kernel handed a function applies it, and its contract says nothing of what the function
     * ends a run for: whole, it is not known. A closure the body builds and hands to one is the
     * body's own, read as run: one dividing by the element it is applied to ends a run where the
     * quotient does.
     */
    @Test
    void aKernelHandedAFunctionIsNotKnownAndAClosureHandedToOneIsReadAsRun() {
        Stdlib rewritten = rewritten(IS_EMPTY_BODY,
                "List.length(xs) == 0 && List.length(List.sortBy(n -> 100 / n, [0])) >= 0");
        LibraryEndings endings = LibraryEndings.of(rewritten);

        assertTrue(((Endings.Known) endings.of(IS_EMPTY)).kinds()
                .contains(AbortKind.DIVISION_BY_ZERO));
        assertEquals(new Endings.NotKnown(),
                endings.of(ValueName.Stdlib.operation("List", "sortBy")));
    }

    /** The same of an operation of the library handed to one by its name. */
    @Test
    void aKernelHandedAnOperationByItsNameIsNotKnown() {
        Stdlib rewritten = rewritten(IS_EMPTY_BODY,
                "List.length(xs) == 0 && List.length(List.sortBy(Int.abs, [1])) >= 0");

        assertEquals(new Endings.NotKnown(), LibraryEndings.of(rewritten).of(IS_EMPTY));
    }

    /** A closure the body builds is read as run wherever the body puts it, applied or not. */
    @Test
    void aClosureTheBodyBuildsIsReadAsRun() {
        Stdlib rewritten = rewritten(IS_EMPTY_BODY,
                "{\n    let f = n -> 100 / n\n    List.length(xs) == 0\n}");

        assertTrue(((Endings.Known) LibraryEndings.of(rewritten).of(IS_EMPTY)).kinds()
                .contains(AbortKind.DIVISION_BY_ZERO));
    }

    /** As shipped, an operation derived from the fold applies the function it is handed. */
    @Test
    void anOperationThroughTheFoldIsNotKnown() {
        assertEquals(new Endings.NotKnown(), LibraryEndings.shipped().of(ANY));
    }

    /**
     * An arithmetic over whole numbers is read at {@code Int}, which builds nothing: a sum shown
     * to stay inside an {@code Int} ends no run, and one that may pass it, or a product, which
     * nothing here reads the reach of, ends one where it passes.
     */
    @Test
    void anArithmeticOverWholeNumbersIsReadAtInt() {
        assertEquals(NONE, LibraryEndings.of(rewritten(IS_EMPTY_BODY,
                "List.length(xs) + 0 == 0")).of(IS_EMPTY));
        Endings passing = new Endings.Known(AbortSet.of(AbortKind.REQUIRED_FORM_HAS_NO_PLACE));
        for (String each : new String[] {"List.length(xs) + 9223372036854775807 == 0",
                "List.length(xs) * 2 == 0"}) {
            assertEquals(passing, LibraryEndings.of(rewritten(IS_EMPTY_BODY, each)).of(IS_EMPTY),
                    each);
        }
    }

    /**
     * Apart from the functions it is handed, the walk ends nothing of its own, and nor does an
     * operation putting together at most one element for each element of a list: what it holds on
     * the way is no longer than the part walked. One putting any number together for each holds
     * as many as the pieces do, and answers where they fit. Read whole, each is the function it
     * applies, which nothing here says.
     */
    @Test
    void apartFromWhatItIsHandedAWalkEndsWhatItsPiecesDo() {
        LibraryEndings endings = LibraryEndings.shipped();
        for (String each : new String[] {"foldFrom", "map", "filter"}) {
            ValueName.Stdlib.Operation operation = ValueName.Stdlib.operation("List", each);
            assertEquals(NONE, endings.apartFromWhatItIsHanded(operation), each);
            assertEquals(new GetsPast.Always(),
                    endings.completionApartFromWhatItIsHanded(operation), each);
            assertEquals(new Endings.NotKnown(), endings.of(operation), each);
        }
        ValueName.Stdlib.Operation flatMap = ValueName.Stdlib.operation("List", "flatMap");
        assertEquals(new Endings.Known(AbortSet.of(AbortKind.REQUIRED_FORM_HAS_NO_PLACE)),
                endings.apartFromWhatItIsHanded(flatMap));
        assertEquals(new GetsPast.WhereTheAnswerFits(LinearForm.atom(new LawNumber.SumOver<>(1,
                        new LawNumber.SizeOf<>(new LawSubject.WhatTheClosureAnswers<>(0))))),
                endings.completionApartFromWhatItIsHanded(flatMap));
    }

    /** A join of two lists answers where the two fit together, and so does an operation whose
     *  body is that join of two of its parameters, in whichever order the body names them. */
    @Test
    void anOperationThatIsAJoinOfItsParametersAnswersWhereTheyFitTogether() {
        GetsPast together = new GetsPast.WhereTheAnswerFits(GetsPast.together(0, 0, 1));
        assertEquals(together,
                LibraryEndings.shipped().completionApartFromWhatItIsHanded(APPEND));
        assertEquals(together, LibraryEndings.of(rewritten(APPEND_BODY, "= b ++ a"))
                .completionApartFromWhatItIsHanded(APPEND));
    }

    /**
     * A filter whose step joins what it carried to itself is no longer one putting together at
     * most one element for each: that is proved of the body, and the body here does not prove it,
     * so what it holds on the way is not bounded by the list and its join is not known to fit.
     */
    @Test
    void aFilterThatDoublesWhatItCarriedIsNotKnownToFit() {
        LibraryEndings endings = LibraryEndings.of(rewritten(
                "if keep(x) then acc ++ [x] else acc", "if keep(x) then acc ++ acc ++ [x] else acc"));
        ValueName.Stdlib.Operation filter = ValueName.Stdlib.operation("List", "filter");

        assertEquals(new Endings.Known(AbortSet.of(AbortKind.REQUIRED_FORM_HAS_NO_PLACE)),
                endings.apartFromWhatItIsHanded(filter));
        assertEquals(new GetsPast.NotKnown(), endings.completionApartFromWhatItIsHanded(filter));
    }

    /**
     * A walk of a list that puts at most one element into what it carries for each element, and
     * adds a number written out to what it counts, holds no more than the list and counts no
     * further than an {@code Int} holds: taking, dropping and filing by a key answer always,
     * apart from the key they are handed.
     */
    @Test
    void aWalkThatPutsInOneForEachElementAnswersAlways() {
        LibraryEndings endings = LibraryEndings.shipped();
        for (String each : new String[] {"take", "drop", "indexBy", "filterMap"}) {
            ValueName.Stdlib.Operation operation = ValueName.Stdlib.operation("List", each);
            assertEquals(NONE, endings.apartFromWhatItIsHanded(operation), each);
            assertEquals(new GetsPast.Always(),
                    endings.completionApartFromWhatItIsHanded(operation), each);
        }
        assertEquals(new Endings.NotKnown(), endings.of(FILTER_MAP));
    }

    /**
     * A walk whose step chooses by a {@code match} puts in what each arm puts in, so one arm
     * putting two in, a choice made by what may end a run, or an element put in that may end
     * one, says nothing of where it answers.
     */
    @Test
    void aWalkChoosingByAMatchAnswersWhatEveryArmDoes() {
        for (String[] rewrite : new String[][] {
                {"| Some v -> acc ++ [v],", "| Some v -> acc ++ [v, v],"},
                {"match f(x) with", "match (if 1 / List.length(acc) == 0 then f(x) else f(x)) with"},
                {"| Some v -> acc ++ [v],",
                        "| Some v -> acc ++ [if 1 / List.length(acc) == 0 then v else v],"}}) {
            LibraryEndings endings = LibraryEndings.of(rewritten(rewrite[0], rewrite[1]));
            assertTrue(!endings.apartFromWhatItIsHanded(FILTER_MAP).endsNone(), rewrite[1]);
            assertEquals(new GetsPast.NotKnown(),
                    endings.completionApartFromWhatItIsHanded(FILTER_MAP), rewrite[1]);
        }
    }

    /**
     * A collection a body builds holds no more than what it is shown to under the way the body
     * went to reach it, and a body answers where what it builds there fits: an insert reached
     * only where the key is there holds no more than the map; one reached either way, one more; a
     * walk starting from a map holds it and one for each entry walked; a walk joining whole
     * lists holds what they hold together; and one filing each element in a list under its key
     * holds, in every list, no more than it has walked, since the list it finds under the key is
     * one of those it filed.
     */
    @Test
    void whatABodyBuildsIsHeldToWhatItIsShownToHoldWhereItIsReached() {
        LibraryEndings endings = LibraryEndings.shipped();
        assertEquals(new GetsPast.Always(), endings.completionApartFromWhatItIsHanded(
                ValueName.Stdlib.operation("List", "groupBy")));
        assertEquals(new GetsPast.Always(), endings.completionApartFromWhatItIsHanded(
                ValueName.Stdlib.operation("Map", "updateIfPresent")));
        assertEquals(new GetsPast.WhereTheAnswerFits(GetsPast.together(1, 3)),
                endings.completionApartFromWhatItIsHanded(
                        ValueName.Stdlib.operation("Map", "updateOrInsert")));
        assertEquals(new GetsPast.WhereTheAnswerFits(GetsPast.together(0, 0, 1)),
                endings.completionApartFromWhatItIsHanded(
                        ValueName.Stdlib.operation("Map", "union")));
        assertEquals(new GetsPast.WhereTheAnswerFits(LinearForm.atom(new LawNumber.SumOver<>(0,
                        new LawNumber.SizeOf<>(new LawSubject.ElementOf<>(0))))),
                endings.completionApartFromWhatItIsHanded(
                        ValueName.Stdlib.operation("List", "concat")));
    }

    /** An operation handed no function is read whole as it is read apart from what it is handed,
     *  and an arithmetic over whole numbers it is handed ends a run where it passes an Int. */
    @Test
    void anOperationHandedNoFunctionIsReadWholeAsItIsReadApart() {
        LibraryEndings endings = LibraryEndings.shipped();
        for (String each : new String[] {"take", "drop", "distinct", "zipShortest", "contains"}) {
            assertEquals(NONE, endings.of(ValueName.Stdlib.operation("List", each)), each);
        }
        assertEquals(new Endings.Known(AbortSet.of(AbortKind.REQUIRED_FORM_HAS_NO_PLACE)),
                endings.of(ValueName.Stdlib.operation("Int", "abs")));
    }

    /** One filing two for an element under a key, whether into the list it finds there or as
     *  the list it starts there, may hold more under the key than it walked, and nothing is said
     *  of where it answers. */
    @Test
    void aWalkFilingTwoForAnElementUnderAKeyIsNotKnownToAnswer() {
        for (String[] rewrite : new String[][] {
                {"| Some bucket -> bucket ++ [x],", "| Some bucket -> bucket ++ [x, x],"},
                {"| None -> [x]\n", "| None -> [x, x]\n"}}) {
            LibraryEndings endings = LibraryEndings.of(rewritten(rewrite[0], rewrite[1]));
            assertEquals(new GetsPast.NotKnown(), endings.completionApartFromWhatItIsHanded(
                    ValueName.Stdlib.operation("List", "groupBy")), rewrite[1]);
        }
    }

    /** A value a step works out and then does not answer is worked out all the same, and what it
     *  holds is asked of as well. */
    @Test
    void aValueAStepWorksOutAndDropsIsAskedOfAsWell() {
        LibraryEndings endings = LibraryEndings.of(rewritten(
                "(acc, x) -> if keep(x) then acc ++ [x] else acc",
                "(acc, x) -> {\n        let twice = acc ++ acc\n"
                        + "        if keep(x) then acc ++ [x] else acc\n    }"));
        ValueName.Stdlib.Operation filter = ValueName.Stdlib.operation("List", "filter");

        assertTrue(!endings.apartFromWhatItIsHanded(filter).endsNone());
        assertEquals(new GetsPast.NotKnown(), endings.completionApartFromWhatItIsHanded(filter));
    }

    /** A site in a closure the body hands to a kernel is met by no reading of the body, so
     *  nothing is shown of what it holds, and it ends a run where it holds too much. */
    @Test
    void aSiteNoReadingMeetsIsNotShownToHoldLittle() {
        Stdlib rewritten = rewritten(IS_EMPTY_BODY,
                "List.length(List.sortBy(y -> List.length(List.append(xs, xs)), [1])) >= 0");

        assertEquals(new Endings.Known(AbortSet.of(AbortKind.REQUIRED_FORM_HAS_NO_PLACE)),
                LibraryEndings.of(rewritten).of(IS_EMPTY));
    }

    /** What a walk is proved to end of its own is what an operation calling it reads, as it reads
     *  any operation it calls. */
    @Test
    void anOperationCallingAWalkProvedToEndNoneEndsNoneApartFromWhatItIsHanded() {
        LibraryEndings endings = LibraryEndings.of(rewritten(ANY_BODY,
                "List.all(p, List.take(1, xs))"));

        assertEquals(NONE, endings.apartFromWhatItIsHanded(ANY));
        assertEquals(new GetsPast.Always(), endings.completionApartFromWhatItIsHanded(ANY));
    }

    /**
     * What a walk counts starts where it is written: one counting by one from as far below the
     * greatest {@code Int} as a list holds elements stays an {@code Int} however many it walks,
     * and one counting from a step nearer, or from the greatest itself, passes it on a list long
     * enough, so nothing is said of where it answers.
     */
    @Test
    void aWalkCountingFromWhereItStartsAnswersOnlyWhereItCannotPassAnInt() {
        ValueName.Stdlib.Operation take = ValueName.Stdlib.operation("List", "take");
        assertEquals(new GetsPast.Always(), LibraryEndings.of(rewritten("(0, [])",
                "(9223372034707292160, [])")).completionApartFromWhatItIsHanded(take));
        for (String seed : new String[] {"9223372034707292161", "9223372036854775807"}) {
            assertEquals(new GetsPast.NotKnown(), LibraryEndings.of(rewritten("(0, [])",
                    "(" + seed + ", [])")).completionApartFromWhatItIsHanded(take), seed);
        }
    }

    /**
     * One joining what it carries to itself may hold more than the list, and nothing is said of
     * where it answers. Filing a value under a key twice is not that: the map already holds the
     * key the second time, and holds no more for it, which the law of an insert says.
     */
    @Test
    void aWalkThatPutsInMoreThanOneIsNotKnownToAnswer() {
        LibraryEndings twice = LibraryEndings.of(rewritten("Map.insert(key(x), x, acc)",
                "Map.insert(key(x), x, Map.insert(key(x), x, acc))"));
        assertEquals(new GetsPast.Always(), twice.completionApartFromWhatItIsHanded(
                ValueName.Stdlib.operation("List", "indexBy")));
        LibraryEndings doubled = LibraryEndings.of(rewritten(
                "if i < n then (next, ys ++ [x]) else (next, ys)",
                "if i < n then (next, ys ++ ys) else (next, ys)"));
        assertEquals(new GetsPast.NotKnown(), doubled.completionApartFromWhatItIsHanded(
                ValueName.Stdlib.operation("List", "take")));
    }

    /** An operation the library does not have is refused, and not answered as not known. */
    @Test
    void anOperationTheLibraryDoesNotHaveIsRefused() {
        assertThrows(IllegalArgumentException.class, () -> LibraryEndings.shipped()
                .of(ValueName.Stdlib.operation("List", "noSuchOperation")));
    }

    private static Stdlib rewritten(String shipped, String body) {
        return rewritten(text -> text.replace(shipped, body));
    }

    /** The library with {@code rewriting} applied, which must change some text of it: a rewrite
     *  that matched nothing would hold the shipped body to what the test says of another. */
    private static Stdlib rewritten(UnaryOperator<String> rewriting) {
        boolean[] changed = {false};
        Stdlib library = StdlibLoader.load(text -> {
            String out = rewriting.apply(text);
            changed[0] |= !out.equals(text);
            return out;
        });
        assertTrue(changed[0], "the rewrite matched nothing the library writes");
        return library;
    }
}
