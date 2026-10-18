package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.abort.AbortKind;
import souther.compiler.abort.AbortSet;
import souther.compiler.check.WhatARunMayEndFor.Endings;
import souther.compiler.core.KernelContracts;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ValueName;

import java.util.function.UnaryOperator;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

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
        assertEquals(NONE, LibraryEndings.of(DefaultStdlib.get()).of(IS_EMPTY));
    }

    /** The same name and signature over a body joining two lists ends a run where the join does. */
    @Test
    void whatTheBodyEndsARunForIsWhatTheOperationDoes() {
        Stdlib rewritten = rewritten(IS_EMPTY_BODY, "List.length(xs ++ xs) == 0");

        assertEquals(new Endings.Known(AbortSet.of(AbortKind.REQUIRED_FORM_HAS_NO_PLACE)),
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

    /** A closure built and never applied runs nothing of its body. */
    @Test
    void aClosureNeverAppliedEndsNoRun() {
        Stdlib rewritten = rewritten(IS_EMPTY_BODY,
                "{\n    let f = n -> 100 / n\n    List.length(xs) == 0\n}");

        assertEquals(NONE, LibraryEndings.of(rewritten).of(IS_EMPTY));
    }

    /** An operation the library does not have is refused, and not answered as not known. */
    @Test
    void anOperationTheLibraryDoesNotHaveIsRefused() {
        assertThrows(IllegalArgumentException.class, () -> LibraryEndings.of(DefaultStdlib.get())
                .of(ValueName.Stdlib.operation("List", "noSuchOperation")));
    }

    private static Stdlib rewritten(String shipped, String body) {
        return rewritten(text -> text.replace(shipped, body));
    }

    private static Stdlib rewritten(UnaryOperator<String> rewriting) {
        return StdlibLoader.load(rewriting);
    }
}
