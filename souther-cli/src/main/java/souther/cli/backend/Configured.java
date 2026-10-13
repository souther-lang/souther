package souther.cli.backend;

/**
 * What the settings name to fetch backends from: a repository that can be asked, or settings that
 * name none.
 */
public sealed interface Configured permits Repository, Configured.Unusable {

    /** What a reader is told the repository is called. */
    String name();

    /**
     * The settings name no repository that can be asked, which {@code why} says. Nothing is asked
     * where this is what was named, so it holds no address to ask.
     */
    record Unusable(String name, Central.Failure.Misconfigured why)
            implements Configured, BackendFetch.Source {}
}
