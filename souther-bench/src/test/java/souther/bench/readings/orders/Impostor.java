package souther.bench.readings.orders;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * A method that is called what a crossing is called and takes what one takes, and puts nothing in
 * an order.
 *
 * <p>What makes a call a crossing is which method it is — the class that declares it, its name and
 * what it takes — and a name alone is what this is here to be passed by.
 */
public final class Impostor {

    private Impostor() {}

    public static <T> List<T> keep(Collection<T> held) {
        return new ArrayList<>(held);
    }
}
