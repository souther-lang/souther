package souther.cli.backend;

import java.net.InetSocketAddress;
import java.net.ProxySelector;
import java.net.URI;
import java.net.URISyntaxException;
import java.net.http.HttpClient;
import java.time.Duration;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * The Maven repository backends are fetched from: where it is, what a reader is told it is called,
 * and how it is reached.
 *
 * <p>Every one of those is read from the settings here, once, and nowhere else. What the run is
 * told by {@code souther.repository}, {@code https.proxyHost}, {@code HTTPS_PROXY} and
 * {@code NO_PROXY} decides them together, so a message naming the repository and the client asking
 * it cannot be reading two versions of one setting.
 *
 * <p>A repository is reached over HTTPS, or over plain HTTP on this machine's own loopback address,
 * and so is every address a redirect from it sends a request to: {@link #admits} is the one place
 * that is decided.
 */
public final class Repository implements Configured {

    /** Where releases are fetched from unless {@code souther.repository} says otherwise. */
    public static final URI MAVEN_CENTRAL = URI.create("https://repo.maven.apache.org/maven2/");

    static final String SETTING = "souther.repository";

    private static final Duration CONNECT = Duration.ofSeconds(15);

    private static final Set<String> LOOPBACK = Set.of("localhost", "127.0.0.1", "[::1]");

    /** How the repository is reached: directly, through a proxy, or as Java's settings say. */
    sealed interface Route {
        record Direct() implements Route {}

        record Through(InetSocketAddress proxy) implements Route {}

        /** Java's own {@code https.proxyHost} and {@code http.nonProxyHosts}. */
        record AsJavaSays() implements Route {}
    }

    private final URI root;
    private final String name;
    private final Route route;
    private HttpClient client;

    private Repository(URI root, String name, Route route) {
        this.root = root;
        this.name = name;
        this.route = route;
    }

    /** The repository this run's settings name, or the setting that names none it can use. */
    public static Configured configured(Map<String, String> environment) {
        String named = System.getProperty(SETTING);
        String name = named == null || named.isBlank() ? "Maven Central" : named;
        Optional<URI> root = named == null || named.isBlank() ? Optional.of(MAVEN_CENTRAL)
                : root(named);
        if (root.isEmpty()) {
            return new Configured.Unusable(name,
                    new Central.Failure.Misconfigured(SETTING, named));
        }
        URI at = root.get();
        if (loopback(at) || bypassed(at.getHost(),
                either(environment, "NO_PROXY", "no_proxy").orElse(""))) {
            return new Repository(at, name, new Route.Direct());
        }
        Optional<String> proxy = either(environment, "HTTPS_PROXY", "https_proxy");
        if (System.getProperty("https.proxyHost") != null || proxy.isEmpty()) {
            return new Repository(at, name, new Route.AsJavaSays());
        }
        Optional<InetSocketAddress> address = proxyAddress(proxy.get());
        return address.isEmpty()
                ? new Configured.Unusable(name,
                        new Central.Failure.Misconfigured("HTTPS_PROXY", proxy.get()))
                : new Repository(at, name, new Route.Through(address.get()));
    }

    /** The repository at {@code root}, reached directly; for a repository a test serves. */
    static Repository at(URI root) {
        return new Repository(root, root.toString(), new Route.Direct());
    }

    /** What a reader is told the repository is called: Maven Central, or the address in its place. */
    @Override
    public String name() {
        return name;
    }

    URI root() {
        return root;
    }

    /** Whether a request may be sent to {@code uri}: over HTTPS, or plain HTTP on the loopback. */
    static boolean admits(URI uri) {
        return "https".equals(uri.getScheme())
                || ("http".equals(uri.getScheme()) && loopback(uri));
    }

    /**
     * The client the repository is asked through, made the first time it is asked for: a run that
     * only names the repository, to say it was not asked, starts no client.
     *
     * <p>It follows no redirect itself. The client's own following refuses only HTTPS to plain
     * HTTP, and would take a repository on the loopback address to plain HTTP anywhere, so
     * {@link Central} follows them and holds each to {@link #admits} before anything is sent.
     */
    synchronized HttpClient client() {
        if (client == null) {
            HttpClient.Builder builder = HttpClient.newBuilder().connectTimeout(CONNECT)
                    .followRedirects(HttpClient.Redirect.NEVER);
            switch (route) {
                case Route.Direct _ -> builder.proxy(HttpClient.Builder.NO_PROXY);
                case Route.Through through -> builder.proxy(ProxySelector.of(through.proxy()));
                case Route.AsJavaSays _ -> { }
            }
            client = builder.build();
        }
        return client;
    }

    /** The repository a setting names, where it names one that may be asked. */
    private static Optional<URI> root(String named) {
        URI uri;
        try {
            uri = new URI(named.endsWith("/") ? named : named + "/");
        } catch (URISyntaxException e) {
            return Optional.empty();
        }
        return uri.isAbsolute() && uri.getHost() != null && admits(uri) ? Optional.of(uri)
                : Optional.empty();
    }

    /** Whether the host is this machine's loopback, as a name or an address, asking no resolver. */
    private static boolean loopback(URI uri) {
        String host = uri.getHost();
        return host != null && LOOPBACK.contains(host.toLowerCase(Locale.ROOT));
    }

    /** The first of the two spellings a variable is set under that is not blank. */
    private static Optional<String> either(Map<String, String> environment, String upper,
                                           String lower) {
        for (String variable : List.of(upper, lower)) {
            String value = environment.get(variable);
            if (value != null && !value.isBlank()) {
                return Optional.of(value.strip());
            }
        }
        return Optional.empty();
    }

    /**
     * Whether {@code NO_PROXY} names the host: a list split at commas, each a host, a domain that
     * covers its subdomains with or without a leading dot, or {@code *} for every host. An empty
     * list names none. The host is one an absolute address has, so it is there.
     */
    static boolean bypassed(String host, String noProxy) {
        String asked = host.toLowerCase(Locale.ROOT);
        for (String entry : noProxy.split(",")) {
            String named = entry.strip().toLowerCase(Locale.ROOT);
            String domain = named.startsWith(".") ? named.substring(1) : named;
            if (named.equals("*") || (!domain.isEmpty()
                    && (asked.equals(domain) || asked.endsWith("." + domain)))) {
                return true;
            }
        }
        return false;
    }

    /** Where {@code HTTPS_PROXY} says the proxy is, written as a URL or as host and port. */
    private static Optional<InetSocketAddress> proxyAddress(String proxy) {
        URI uri;
        try {
            uri = new URI(proxy.contains("://") ? proxy : "http://" + proxy);
        } catch (URISyntaxException e) {
            return Optional.empty();
        }
        if (uri.getHost() == null) {
            return Optional.empty();
        }
        int port = uri.getPort() >= 0 ? uri.getPort() : "https".equals(uri.getScheme()) ? 443 : 80;
        return Optional.of(InetSocketAddress.createUnresolved(uri.getHost(), port));
    }
}
