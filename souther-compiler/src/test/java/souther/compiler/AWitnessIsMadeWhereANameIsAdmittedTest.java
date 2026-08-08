package souther.compiler;

import souther.compiler.check.BoundaryInput;
import souther.compiler.check.BoundaryMapKey;
import souther.compiler.check.BoundaryOutput;
import souther.compiler.check.Sig;
import souther.compiler.types.MapKeyRepresentation;
import souther.compiler.types.TypeName;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Constructor;
import java.lang.reflect.Modifier;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A boundary witness that names a type is made where that name is admitted, and nowhere else. What a
 * witness is worth is that it exists: a reader is handed one and reads it, rather than asking again
 * whether the name in it is one the boundary carries.
 *
 * <p>Held by asking for the constructor rather than by calling it, since a caller outside the
 * package does not compile — this test lives in one, so what it can say is that the door is shut.
 * Every case that names a type is here; a case that names none stands for a representation the
 * boundary always admits, so there is nothing it could be assembled into that is refused.
 */
class AWitnessIsMadeWhereANameIsAdmittedTest {

    @Test
    void aSignatureIsMadeOnlyByTheWalkThatAdmitsIt() throws Exception {
        assertClosed(Sig.class, List.class, BoundaryOutput.class);
    }

    @Test
    void anInputNamingATypeIsMadeOnlyWhereThatNameIsAdmitted() throws Exception {
        assertClosed(BoundaryInput.Nominal.class, TypeName.class);
    }

    @Test
    void anOutputNamingATypeIsMadeOnlyWhereThatNameIsAdmitted() throws Exception {
        assertClosed(BoundaryOutput.Nominal.class, TypeName.class);
        assertClosed(BoundaryOutput.Cases.class, List.class);
    }

    @Test
    void anAdmittedMapKeyIsMadeOnlyWhereItsPositionAdmittedIt() throws Exception {
        assertClosed(BoundaryMapKey.class, MapKeyRepresentation.class);
    }

    private static void assertClosed(Class<?> witness, Class<?>... parameters) throws Exception {
        Constructor<?> ctor = witness.getDeclaredConstructor(parameters);
        assertFalse(Modifier.isPublic(ctor.getModifiers()),
                witness.getSimpleName() + " can be assembled from outside the package that admits"
                        + " what it names, so holding one is no longer evidence of anything");
    }
}
