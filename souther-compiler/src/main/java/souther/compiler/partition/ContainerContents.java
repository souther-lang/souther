package souther.compiler.partition;

import java.util.List;

/**
 * The values a container being composed is to hold, and the values it is to hold nothing equal to.
 *
 * <p>Values and not where they came from. That a list holds what another parameter was composed
 * as is the caller's to work out; what a container is built from is these, whatever position they
 * were read at.
 *
 * @param holding the values written into it, each as one element
 * @param keptOut the values no element of it is equal to
 */
record ContainerContents(List<FixtureTemplate> holding, List<FixtureTemplate> keptOut) {

    ContainerContents {
        holding = List.copyOf(holding);
        keptOut = List.copyOf(keptOut);
    }
}
