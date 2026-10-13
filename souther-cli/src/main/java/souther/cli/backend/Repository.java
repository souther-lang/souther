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
public final class Repository {

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
    private final Central.Failure.Misconfigured misconfigured;
    private HttpClient client;

    private Repository(URI root, String name, Route route,
                       Central.Failure.Misconfigured misconfigured) {
        this.root = root;
        this.name = name;
        this.route = route;
        this.misconfigured = misconfigured;
    }

    /** The repository this run's settings name, or the setting that names none it can use. */
    public static Repository configured(Map<String, String> environment) {
        String named = System.getProperty(SETTING);
        URI root = MAVEN_CENTRAL;
        String name = "Maven Central";
        if (named != null && !named.isBlank()) {
            name = named;
            root = root(named);
            if (root == null) {
                return new Repository(MAVEN_CENTRAL, name, new Route.Direct(),
                        new Central.Failure.Misconfigured(SETTING, named));
            }
        }
        if (loopback(root)
                || bypassed(root.getHost(), either(environment, "NO_PROXY", "no_proxy"))) {
            return new Repository(root, name, new Route.Direct(), null);
        }
        if (System.getProperty("https.proxyHost") != null) {
            return new Repository(root, name, new Route.AsJavaSays(), null);
        }
        String proxy = either(environment, "HTTPS_PROXY", "https_proxy");
        if (proxy == null) {
            return new Repository(root, name, new Route.AsJavaSays(), null);
        }
        InetSocketAddress address = proxyAddress(proxy);
        return address == null
                ? new Repository(root, name, new Route.Direct(),
                        new Central.Failure.Misconfigured("HTTPS_PROXY", proxy))
                : new Repository(root, name, new Route.Through(address), null);
    }

    /** The repository at {@code root}, reached directly; for a repository a test serves. */
    static Repository at(URI root) {
        return new Repository(root, root.toString(), new Route.Direct(), null);
    }

    /** What a reader is told the repository is called: Maven Central, or the address in its place. */
    public String name() {
        return name;
    }

    URI root() {
        return root;
    }

    /** The setting that names nothing this can ask, or null where the repository can be asked. */
    Central.Failure.Misconfigured misconfigured() {
        return misconfigured;
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

    private static URI root(String named) {
        URI uri;
        try {
            uri = new URI(named.endsWith("/") ? named : named + "/");
        } catch (URISyntaxException e) {
            return null;
        }
        return uri.isAbsolute() && uri.getHost() != null && admits(uri) ? uri : null;
    }

    /** Whether the host is this machine's loopback, as a name or an address, asking no resolver. */
    private static boolean loopback(URI uri) {
        String host = uri.getHost();
        return host != null && LOOPBACK.contains(host.toLowerCase(Locale.ROOT));
    }

    /** The first of the two spellings a variable is set under that is not blank, or null. */
    private static String either(Map<String, String> environment, String upper, String lower) {
        for (String variable : List.of(upper, lower)) {
            String value = environment.get(variable);
            if (value != null && !value.isBlank()) {
                return value.strip();
            }
        }
        return null;
    }

    /**
     * Whether {@code NO_PROXY} names the host: a list split at commas, each a host, a domain that
     * covers its subdomains with or without a leading dot, or {@code *} for every host.
     */
    static boolean bypassed(String host, String noProxy) {
        if (host == null || noProxy == null) {
            return false;
        }
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
    private static InetSocketAddress proxyAddress(String proxy) {
        URI uri;
        try {
            uri = new URI(proxy.contains("://") ? proxy : "http://" + proxy);
        } catch (URISyntaxException e) {
            return null;
        }
        if (uri.getHost() == null) {
            return null;
        }
        int port = uri.getPort() >= 0 ? uri.getPort() : "https".equals(uri.getScheme()) ? 443 : 80;
        return InetSocketAddress.createUnresolved(uri.getHost(), port);
    }
}
