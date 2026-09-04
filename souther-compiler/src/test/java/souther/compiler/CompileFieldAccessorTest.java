package souther.compiler;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Spec §field-visibility, §jvm-product: a data gets a public record-style read accessor {@code <field>()} per
 * field, so an exposed one is readable across the module (package) boundary and from Java. A data the module
 * keeps to itself has them too — a record's component is read through its accessor, and the class is out of a
 * Java caller's reach anyway — but its class is package-private, so nothing outside can call them. The
 * constructor stays non-public either way, so a read never enables construction.
 */
class CompileFieldAccessorTest {

    private static Object decodeMember(Class<?> member) throws Exception {
        return Codecs.decoded(member, Map.of("id", "m-1", "age", 30L));
    }

    @Test
    void exposedDataGetsPublicFieldAccessors() throws Exception {
        String src = """
                module demo
                exposing ( Id, Member )

                data Id = String
                data Member = { id: Id, age: Int }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Class<?> member = loader.loadClass("demo.Member");
        Object m = decodeMember(member);

        Method age = member.getMethod("age");
        assertTrue(Modifier.isPublic(age.getModifiers()), "accessor is public");
        assertEquals(30L, age.invoke(m));

        Object id = member.getMethod("id").invoke(m);
        assertEquals("demo.Id", id.getClass().getName());
    }

    @Test
    void aNonExposedDataKeepsItsAccessorsBehindAPackagePrivateClass() throws Exception {
        String src = """
                module demo
                exposing ( Id, Member )

                data Id = String
                data Member = { id: Id }
                data Secret = { code: String }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Class<?> secret = loader.loadClass("demo.Secret");

        assertTrue(Modifier.isPublic(secret.getMethod("code").getModifiers()), "accessor is public");
        assertFalse(Modifier.isPublic(secret.getModifiers()),
                "the class is not, so nothing outside the module can call it");
    }
}
