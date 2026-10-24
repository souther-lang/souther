package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.abort.AbortKind;
import souther.compiler.abort.AbortSet;
import souther.compiler.abort.GetsPast;
import souther.compiler.check.WhatARunMayEndFor.Endings;
import souther.compiler.core.KernelContracts;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ValueName;

import java.util.List;
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

    /** A quotient builds nothing, so what it ends a run for is said whatever its operands are. */
    @Test
    void aQuotientEndsARunForWhatItsSitesDo() {
        Stdlib rewritten = rewritten(IS_EMPTY_BODY, "List.length(xs) / 1 >= 0");

        assertEquals(new Endings.Known(AbortSet.of(AbortKind.DIVISION_BY_ZERO,
                        AbortKind.REQUIRED_FORM_HAS_NO_PLACE)),
                LibraryEndings.of(rewritten).of(IS_EMPTY));
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
     * ends a run for: a closure dividing by the element it is applied to is handed to one here.
     */
    @Test
    void aKernelHandedAFunctionIsNotKnown() {
        Stdlib rewritten = rewritten(IS_EMPTY_BODY,
                "List.length(xs) == 0 && List.length(List.sortBy(n -> 100 / n, [0])) >= 0");
        LibraryEndings endings = LibraryEndings.of(rewritten);

        assertEquals(new Endings.NotKnown(), endings.of(IS_EMPTY));
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

    /** A closure built and never applied runs nothing of its body. */
    @Test
    void aClosureNeverAppliedEndsNoRun() {
        Stdlib rewritten = rewritten(IS_EMPTY_BODY,
                "{\n    let f = n -> 100 / n\n    List.length(xs) == 0\n}");

        assertEquals(NONE, LibraryEndings.of(rewritten).of(IS_EMPTY));
    }

    /** As shipped, an operation derived from the fold applies the function it is handed. */
    @Test
    void anOperationThroughTheFoldIsNotKnown() {
        assertEquals(new Endings.NotKnown(), LibraryEndings.shipped().of(ANY));
    }

    /**
     * {@code + - *} over a newtype build it again, and what a construction ends a run for is its
     * declaration's: a body whose operands carry no type may be building one.
     */
    @Test
    void anArithmeticThatMayBuildANewtypeIsNotKnown() {
        Stdlib rewritten = rewritten(IS_EMPTY_BODY, "List.length(xs) + 0 == 0");

        assertEquals(new Endings.NotKnown(), LibraryEndings.of(rewritten).of(IS_EMPTY));
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
        assertEquals(new GetsPast.WhereTheAnswerFits(new GetsPast.AnswerSize.PiecesOf(1, 0)),
                endings.completionApartFromWhatItIsHanded(flatMap));
    }

    /** A join of two lists answers where the two fit together, and so does an operation whose
     *  body is that join of two of its parameters, in the order the body names them. */
    @Test
    void anOperationThatIsAJoinOfItsParametersAnswersWhereTheyFitTogether() {
        assertEquals(new GetsPast.WhereTheAnswerFits(
                        new GetsPast.AnswerSize.SumOf(List.of(0, 1), 0)),
                LibraryEndings.shipped().completionApartFromWhatItIsHanded(APPEND));
        assertEquals(new GetsPast.WhereTheAnswerFits(
                        new GetsPast.AnswerSize.SumOf(List.of(1, 0), 0)),
                LibraryEndings.of(rewritten(APPEND_BODY, "= b ++ a"))
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
        for (String each : new String[] {"take", "drop", "indexBy"}) {
            assertEquals(new GetsPast.Always(), endings.completionApartFromWhatItIsHanded(
                    ValueName.Stdlib.operation("List", each)), each);
        }
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

    /** One putting two in for an element, or joining what it carries to itself, may hold more
     *  than the list, and nothing is said of where it answers. */
    @Test
    void aWalkThatPutsInMoreThanOneIsNotKnownToAnswer() {
        LibraryEndings twice = LibraryEndings.of(rewritten("Map.insert(key(x), x, acc)",
                "Map.insert(key(x), x, Map.insert(key(x), x, acc))"));
        assertEquals(new GetsPast.NotKnown(), twice.completionApartFromWhatItIsHanded(
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
