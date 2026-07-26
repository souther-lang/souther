// The HTTP boundary for fulfilment, and what the deepened module graph looks like from Java. One
// request crosses four Souther modules at three import depths — cart's quote, ordering's place,
// inventory's Location as a shelf code, and shipping's planPicks — and the controller composes them
// the same way it composes any two: run one, match its output, run the next.
//
// Nothing about the depth shows up here. shipping imports inventory which imports cart, and the
// generated classes are just classes; there is no ordering the caller has to respect and no module
// boundary the values have to be converted across. What the boundary still does is what it always
// does: decode, orchestrate, encode.
//
// The shelf map is decoded key by key. `Map<Sku, Location>` reaches Java as a Map of the two
// generated types, so each key runs Sku's invariant and each value runs Location's — a malformed
// shelf code is a 400 here, not a bad pick list later.
package app.ordering.web;

import example.cart.Cart;
import example.cart.EmptyCart;
import example.cart.InvalidQuantity;
import example.cart.PricedCart;
import example.cart.Quote;
import example.cart.Sku;
import example.inventory.Location;
import example.ordering.ConfirmedOrder;
import example.ordering.OutOfStock;
import example.ordering.Place;
import example.shipping.NothingToShip;
import example.shipping.PickList;
import example.shipping.PlanPicks;

import net.unit8.raoh.Err;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Path;
import net.unit8.raoh.Result;

import org.springframework.http.ResponseEntity;
import org.springframework.transaction.support.TransactionTemplate;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.RequestBody;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RestController;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * {@code POST /fulfilment}. The body is {@code {"cart": {...}, "shelf": {"<sku>": "<location>"}}}.
 * The cart is priced (example.cart), placed inside a transaction (example.ordering), and the
 * confirmed order's lines are turned into a shelf-ordered pick list (example.shipping, which reads
 * example.inventory's Location).
 *
 * <p>Statuses: a pick list = 201 / nothing pickable = 422 / out of stock = 409 / an empty or invalid
 * cart = 422 / a decode failure, including a malformed sku or shelf code = 400.
 */
@RestController
@RequestMapping("/fulfilment")
public final class FulfilmentController {

    private final Quote quote;
    private final Place place;
    private final PlanPicks planPicks;
    private final TransactionTemplate tx;

    public FulfilmentController(Quote quote, Place place, PlanPicks planPicks, TransactionTemplate tx) {
        this.quote = quote;
        this.place = place;
        this.planPicks = planPicks;
        this.tx = tx;
    }

    @PostMapping
    public ResponseEntity<Object> fulfil(@RequestBody Map<String, Object> body) {
        if (!(body.get("cart") instanceof Map) || !(body.get("shelf") instanceof Map)) {
            return ResponseEntity.badRequest().body(Map.of("error", "cart_and_shelf_required"));
        }
        @SuppressWarnings("unchecked")   // Jackson hands the request body over as a nested Map
        Map<String, Object> rawCart = (Map<String, Object>) body.get("cart");
        Map<?, ?> rawShelf = (Map<?, ?>) body.get("shelf");
        Map<Sku, Location> shelf;
        try {
            shelf = decodeShelf(rawShelf);
        } catch (BadShelf e) {
            return ResponseEntity.badRequest().body(Map.of("error", "invalid_shelf", "at", e.at));
        }

        return switch (Cart.decoder().decode(rawCart, Path.ROOT)) {
            case Err<Cart> _ -> ResponseEntity.badRequest().body(Map.of("error", "invalid_cart"));
            case Ok<Cart>(var cart) -> switch (quote.apply(cart)) {
                case PricedCart priced -> tx.execute(status -> switch (place.apply(priced)) {
                    // The order is placed; the same priced cart is what the warehouse walks.
                    case ConfirmedOrder _ -> switch (planPicks.apply(priced, shelf)) {
                        case PickList picks ->
                                ResponseEntity.status(201).body(PickList.encoder().encode(picks));
                        case NothingToShip _ -> {
                            status.setRollbackOnly();   // nothing to pick: do not keep the order
                            yield ResponseEntity.status(422).body(Map.of("error", "nothing_to_ship"));
                        }
                    };
                    case OutOfStock _ -> {
                        status.setRollbackOnly();
                        yield ResponseEntity.status(409).body(Map.of("error", "out_of_stock"));
                    }
                });
                case EmptyCart _ -> ResponseEntity.status(422).body(Map.of("error", "empty_cart"));
                case InvalidQuantity _ ->
                        ResponseEntity.status(422).body(Map.of("error", "invalid_quantity"));
            };
        };
    }

    /** Each key through {@code Sku}'s decoder and each value through {@code Location}'s, so both
     *  invariants run at the boundary rather than on the way out of it. */
    private static Map<Sku, Location> decodeShelf(Map<?, ?> raw) {
        Map<Sku, Location> shelf = new LinkedHashMap<>();
        for (Map.Entry<?, ?> e : raw.entrySet()) {
            String key = String.valueOf(e.getKey());
            Result<Sku> sku = Sku.decoder().decode(key, Path.ROOT);
            Result<Location> location = Location.decoder().decode(e.getValue(), Path.ROOT);
            if (!(sku instanceof Ok<Sku>(var s)) || !(location instanceof Ok<Location>(var l))) {
                throw new BadShelf(key);
            }
            shelf.put(s, l);
        }
        return shelf;
    }

    /** A shelf entry that did not decode, carrying the key it was under. */
    private static final class BadShelf extends RuntimeException {
        private final String at;

        private BadShelf(String at) {
            super(at, null, false, false);
            this.at = at;
        }
    }
}
