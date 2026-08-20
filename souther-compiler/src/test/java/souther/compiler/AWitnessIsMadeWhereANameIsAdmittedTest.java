package souther.compiler;

import souther.compiler.check.BoundaryInput;
import souther.compiler.check.BoundaryOutput;
import souther.compiler.check.CrossingMapKey;
import souther.compiler.check.CrossingNominal;
import souther.compiler.check.Sig;
import souther.compiler.types.MapKeyRepresentation;
import souther.compiler.types.TypeSymbol;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Constructor;
import java.lang.reflect.Modifier;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A witness that names a type is made where that name is admitted, and nowhere else. What a witness
 * is worth is that it exists: a reader is handed one and reads it, rather than asking again whether
 * the name in it is one that may cross.
 *
 * <p>Two doors, and both are shut. {@link CrossingNominal} is the rule — a named type that crosses is
 * one a model declares — and it is made by its own admission alone, so no walk anywhere can produce
 * one by holding a {@link TypeSymbol}. The witnesses a behavior's boundary hands to its readers are
 * closed on top of that, because being made says this position asked; a shape assembled elsewhere in
 * the package from an admitted name would be a signature nothing established. What a data field's
 * walk builds is closed by the first door only, which is what lets it live in another package:
 * {@code CodecShape.Named} takes the witness and nothing else, so there is no name for it to hope a
 * codec is there for.
 *
 * <p>Held by asking for the constructor rather than by calling it, since a caller outside the
 * package does not compile — this test lives in one, so what it can say is that the door is shut.
 * Every case that names a type is here; a case that names none stands for a representation always
 * admitted, so there is nothing it could be assembled into that is refused.
 */
class AWitnessIsMadeWhereANameIsAdmittedTest {

    @Test
    void aNameThatMayCrossIsMadeByItsAdmissionAlone() throws Exception {
        assertClosed(CrossingNominal.class, TypeSymbol.class);
    }

    @Test
    void aSignatureIsMadeOnlyByTheWalkThatAdmitsIt() throws Exception {
        assertClosed(Sig.class, List.class, BoundaryOutput.class);
    }

    @Test
    void anInputNamingATypeIsMadeOnlyWhereThatNameIsAdmitted() throws Exception {
        assertClosed(BoundaryInput.Nominal.class, CrossingNominal.class);
    }

    @Test
    void anOutputNamingATypeIsMadeOnlyWhereThatNameIsAdmitted() throws Exception {
        assertClosed(BoundaryOutput.Nominal.class, CrossingNominal.class);
        assertClosed(BoundaryOutput.Cases.class, List.class);
    }

    @Test
    void anAdmittedMapKeyIsMadeOnlyFromWhatItsPositionAdmitted() throws Exception {
        assertClosed(CrossingMapKey.class, MapKeyRepresentation.class);
    }

    private static void assertClosed(Class<?> witness, Class<?>... parameters) throws Exception {
        Constructor<?> ctor = witness.getDeclaredConstructor(parameters);
        assertFalse(Modifier.isPublic(ctor.getModifiers()),
                witness.getSimpleName() + " can be assembled from outside the package that admits"
                        + " what it names, so holding one is no longer evidence of anything");
    }
}
