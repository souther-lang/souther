package souther.compiler.abort;

import souther.compiler.DefaultStdlib;
import souther.compiler.core.Core;
import souther.compiler.core.KernelContracts;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.WrittenOwner;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A type {@link AbortSites} was not told a construction builds is refused wherever it is asked about,
 * and never answered as {@link AbortSet#NONE}: "has no invariant" and "nobody said" are not one fact.
 *
 * <p>Built by hand, because a checked program lists every declaration it has and so never reaches
 * the refusal. What is fixed here is that a list of fewer types than a program constructs — one
 * collected from the constructions a walk met, say — fails loudly instead of answering for the types
 * it left out.
 */
class ATypeNobodyListedIsNotAnsweredAsEndingNothingTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final TypeSymbol.AtModule PERSON = TypeSymbols.declared(new TypeKey("demo", "Person"));
    private static final TypeSymbol.AtModule PLAIN = TypeSymbols.declared(new TypeKey("demo", "Plain"));
    private static final KernelContracts KERNELS =
            KernelContracts.of(DefaultStdlib.get().kernelSignatures());

    private static Core.Construct construction(TypeSymbol.AtModule type) {
        return new Core.Construct(type, List.of(new Core.FieldValue("age",
                new Core.Int(1, Type.INT, POS), POS)), Type.ref(type), POS);
    }

    @Test
    void aListedTypeIsAnsweredByWhetherItHoldsAnInvariant() {
        AbortSites sites = AbortSites.of(List.of(), KERNELS,
                List.of(new Constructible(PERSON, true), new Constructible(PLAIN, false)));

        assertEquals(AbortSet.of(AbortKind.INVARIANT_NOT_HELD), sites.ordinaryConstructionOf(PERSON));
        assertEquals(AbortSet.NONE, sites.ordinaryConstructionOf(PLAIN));
    }

    @Test
    void anUnlistedTypeAskedOfByAnOutputIsRefused() {
        AbortSites sites = AbortSites.of(List.of(), KERNELS, List.of(new Constructible(PLAIN, false)));

        assertThrows(IllegalArgumentException.class, () -> sites.ordinaryConstructionOf(PERSON));
    }

    @Test
    void aConstructionOfAnUnlistedTypeIsRefused() {
        assertThrows(IllegalStateException.class, () -> AbortSites.of(
                List.of(construction(PERSON)), KERNELS, List.of(new Constructible(PLAIN, false))));
    }

    /** A guard standing over it does not make the type one somebody listed. */
    @Test
    void soIsOneAnAttemptTests() {
        SourceConstructOrigin origin = SourceConstructOrigin.written(
                new WrittenOwner.Body("demo", "go"), 0, SourceConstruct.IF);
        Core.IfConstructed attempt = new Core.IfConstructed(construction(PERSON),
                new Core.Binder("p", new BindingId(new BindingOwner.OfValue("demo", "go"), 0)),
                new Core.Int(0, Type.INT, POS),
                List.of(new Core.ElseArm(Optional.empty(), new Core.Int(1, Type.INT, POS))),
                Core.ForkPlace.asWritten(ConstructOccurrence.asWritten(origin)), Type.INT, POS);

        assertThrows(IllegalStateException.class,
                () -> AbortSites.of(List.of(attempt), KERNELS, List.of()));
    }

    @Test
    void aTypeListedTwiceIsRefused() {
        assertThrows(IllegalArgumentException.class, () -> AbortSites.of(List.of(), KERNELS,
                List.of(new Constructible(PLAIN, false), new Constructible(PLAIN, true))));
    }
}
