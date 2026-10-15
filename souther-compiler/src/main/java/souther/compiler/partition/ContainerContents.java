package souther.compiler.partition;

import java.util.List;

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
 *                      own over whatever value the rules admit
 * @param keysKeptOut   the values no key of the map is equal to
 */
record ContainerContents(List<FixtureTemplate> holding, List<FixtureTemplate> keptOut,
                         List<FixtureTemplate> keysHeld, List<FixtureTemplate> keysEachFiled,
                         List<FixtureTemplate> keysKeptOut) {

    ContainerContents {
        holding = List.copyOf(holding);
        keptOut = List.copyOf(keptOut);
        keysHeld = List.copyOf(keysHeld);
        keysEachFiled = List.copyOf(keysEachFiled);
        keysKeptOut = List.copyOf(keysKeptOut);
    }
}
