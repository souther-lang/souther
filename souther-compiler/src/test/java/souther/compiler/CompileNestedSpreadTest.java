package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A spread may name a field path ({@code ...c.address}), not only a local. Rebuilding a record
 * nested one level down is the ordinary "change one field of a sub-record" edit, and without this it
 * takes a `let` binding to name the sub-record first.
 */
class CompileNestedSpreadTest {

    @Test
    void aSpreadTakesAFieldPath() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data Address = { city: String, street: String }
                data Customer = { name: String, address: Address }

                behavior move : (c: Customer, city: String) -> Customer constructs Customer, Address

                let move (c, city) = Customer { ...c, address = Address { ...c.address, city = city } }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.Customer", Map.of(
                "name", "A", "address", Map.of("city", "Tokyo", "street", "1-2-3")));
        Class<?> impl = Emitted.behavior(loader, "demo", "move");
        Object out = impl.getMethod("apply", Object.class, Object.class)
                .invoke(impl.getConstructor().newInstance(), in, "Osaka");

        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Customer", out);
        assertEquals("A", m.get("name"));
        assertEquals(Map.of("city", "Osaka", "street", "1-2-3"), m.get("address"),
                "the untouched field comes from the spread path");
    }

    @Test
    void aDeeperPathAlsoSpreads() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data Geo = { lat: String, lon: String }
                data Address = { city: String, geo: Geo }
                data Customer = { name: String, address: Address }
                data Out = { geo: Geo }

                behavior movePin : (c: Customer, lat: String) -> Out constructs Out, Geo

                let movePin (c, lat) = Out { geo = Geo { ...c.address.geo, lat = lat } }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.Customer", Map.of(
                "name", "A",
                "address", Map.of("city", "Tokyo", "geo", Map.of("lat", "1", "lon", "2"))));
        Class<?> impl = Emitted.behavior(loader, "demo", "movePin");
        Object out = impl.getMethod("apply", Object.class, Object.class)
                .invoke(impl.getConstructor().newInstance(), in, "9");

        Map<?, ?> m = (Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
        assertEquals(Map.of("lat", "9", "lon", "2"), m.get("geo"));
    }
}
