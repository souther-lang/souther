package app.ordering;

import org.jooq.DSLContext;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.context.SpringBootTest;
import org.springframework.core.env.Environment;

import java.net.URI;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.nio.charset.StandardCharsets;

import static org.jooq.impl.DSL.field;
import static org.jooq.impl.DSL.name;
import static org.jooq.impl.DSL.table;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Drives {@code POST /fulfilment} over real HTTP, which is one request across four Souther modules at
 * three import depths: cart's quote, ordering's place, inventory's Location, and shipping's planPicks
 * (shipping imports inventory, which imports cart).
 *
 * <p>The load-bearing check is the pick order. {@code planPicks} sorts by {@code Location}, a
 * String-backed newtype, so the response walks the aisles in shelf order rather than in the order the
 * lines were sent — the ordering the language gives a newtype, arriving intact at the boundary.
 */
@SpringBootTest(webEnvironment = SpringBootTest.WebEnvironment.RANDOM_PORT)
class FulfilmentTest {

    @Autowired DSLContext dsl;
    @Autowired Environment env;

    private final HttpClient http = HttpClient.newHttpClient();

    @BeforeEach
    void reset() {
        dsl.deleteFrom(table(name("orders"))).execute();
        dsl.deleteFrom(table(name("order_lines"))).execute();
        setStock("apple", 10);
        setStock("tv", 3);
    }

    @Test
    void POST_returns201_withThePickListInShelfOrder() throws Exception {
        // tv is sent first but sits in aisle C; apple sits in aisle A, so the walk starts there.
        HttpResponse<String> res = post("""
                {"cart": {"open": true, "items": [
                    {"sku": "tv", "quantity": 1, "unitPrice": 200000},
                    {"sku": "apple", "quantity": 2, "unitPrice": 150}]},
                 "shelf": {"tv": "C-01-01", "apple": "A-03-12"}}
                """);

        assertEquals(201, res.statusCode(), res.body());
        assertTrue(res.body().indexOf("A-03-12") < res.body().indexOf("C-01-01"),
                "the pick list is in shelf order, not line order: " + res.body());
        assertEquals(1, orderCount(), "the order is committed");
    }

    @Test
    void POST_returns422_andRollsBack_whenNothingHasAShelf() throws Exception {
        // Both skus are orderable and in stock, but neither has a shelf, so there is no walk to make
        // and the order is not kept.
        HttpResponse<String> res = post("""
                {"cart": {"open": true, "items": [
                    {"sku": "apple", "quantity": 2, "unitPrice": 150}]},
                 "shelf": {"tv": "C-01-01"}}
                """);

        assertEquals(422, res.statusCode(), res.body());
        assertTrue(res.body().contains("nothing_to_ship"), res.body());
        assertEquals(0, orderCount(), "the order rolled back with the failed pick");
    }

    @Test
    void POST_returns400_whenAShelfCodeIsMalformed() throws Exception {
        // "A-3-12" is one digit short of Location's format. The invariant runs at the boundary, so the
        // request is rejected before anything is placed.
        HttpResponse<String> res = post("""
                {"cart": {"open": true, "items": [
                    {"sku": "apple", "quantity": 2, "unitPrice": 150}]},
                 "shelf": {"apple": "A-3-12"}}
                """);

        assertEquals(400, res.statusCode(), res.body());
        assertTrue(res.body().contains("invalid_shelf"), res.body());
        assertEquals(0, orderCount(), "nothing was placed");
    }

    @Test
    void POST_returns409_whenTheOrderCannotBeReserved() throws Exception {
        HttpResponse<String> res = post("""
                {"cart": {"open": true, "items": [
                    {"sku": "tv", "quantity": 5, "unitPrice": 200000}]},
                 "shelf": {"tv": "C-01-01"}}
                """);

        assertEquals(409, res.statusCode(), res.body());
        assertEquals(3, stockOf("tv"), "stock is untouched");
    }

    private HttpResponse<String> post(String json) throws Exception {
        int port = env.getRequiredProperty("local.server.port", Integer.class);
        HttpRequest req = HttpRequest.newBuilder()
                .uri(URI.create("http://localhost:" + port + "/fulfilment"))
                .header("Content-Type", "application/json; charset=UTF-8")
                .POST(HttpRequest.BodyPublishers.ofString(json, StandardCharsets.UTF_8))
                .build();
        return http.send(req, HttpResponse.BodyHandlers.ofString(StandardCharsets.UTF_8));
    }

    private void setStock(String sku, int qty) {
        dsl.mergeInto(table(name("stock")))
                .columns(field(name("sku")), field(name("qty")))
                .key(field(name("sku")))
                .values(sku, qty)
                .execute();
    }

    private int stockOf(String sku) {
        return dsl.select(field(name("qty"), Integer.class))
                .from(table(name("stock")))
                .where(field(name("sku"), String.class).eq(sku))
                .fetchOne(0, Integer.class);
    }

    private int orderCount() {
        return dsl.fetchCount(table(name("orders")));
    }
}
