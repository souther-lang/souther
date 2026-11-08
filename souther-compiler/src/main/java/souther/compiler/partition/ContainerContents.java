package souther.compiler.partition;

import java.math.BigDecimal;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * The values a container being composed is to hold, and the values it is to hold nothing equal to.
 *
 * <p>Values and not where they came from. That a list holds what another parameter was composed
 * as is the caller's to work out; what a container is built from is these, whatever position they
 * were read at.
 *
 * @param holding       the values written into it, each as one element
 * @param keptOut       the values no element of it is equal to
 * @param keysHeld      the values a map is to file an entry under, each a key of its own, asked
 *                      of the one entry some entry is — the one holding the element placed in it,
 *                      where one is
 * @param keysEachFiled the values a map is to file an entry under, each asked of an entry of its
 *                      own over whatever value the rules admit, or the value the rules name
 * @param keysKeptOut   the values no key of the map is equal to
 */
record ContainerContents(List<FixtureTemplate> holding, List<FixtureTemplate> keptOut,
                         List<KeyAsked> keysHeld, List<KeyAsked> keysEachFiled,
                         List<FixtureTemplate> keysKeptOut) {

    ContainerContents {
        holding = List.copyOf(holding);
        keptOut = List.copyOf(keptOut);
        keysHeld = List.copyOf(keysHeld);
        keysEachFiled = List.copyOf(keysEachFiled);
        keysKeptOut = List.copyOf(keysKeptOut);
    }

    /**
     * A key a map is to file an entry under, and the number the rules say the value under it is.
     *
     * @param key     the key
     * @param valueIs the number the value filed under it is to be; empty where any value the rules
     *                admit will do
     */
    record KeyAsked(FixtureTemplate key, Optional<BigDecimal> valueIs) {

        KeyAsked {
            Objects.requireNonNull(key, "a key is asked for");
            Objects.requireNonNull(valueIs, "a number asked of the value under it, or none");
        }
    }
}
