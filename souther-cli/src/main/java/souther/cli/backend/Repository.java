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

    /**
     * The repository this run's settings name, or the setting that names none it can use: the
     * environment {@code variables} and system {@code properties} the run is given.
     */
    public static Configured configured(Map<String, String> variables,
                                        Map<String, String> properties) {
        String named = properties.get(SETTING);
        boolean central = named == null || named.isBlank();
        URI at;
        switch (central ? new Named.At<>(MAVEN_CENTRAL) : root(named)) {
            case Named.At<URI>(URI value) -> at = value;
            case Named.Not<URI>(Central.Failure.Misread why) -> {
                // Called by the setting, since what it was set to read as no repository and is
                // not repeated.
                return new Configured.Unusable(SETTING,
                        new Central.Failure.Misconfigured(SETTING, why));
            }
        }
        // Called by what the setting was read as, rebuilt, and never by what it was written as.
        String name = central ? "Maven Central" : Shown.address(at);
        if (loopback(at) || bypassed(at.getHost(),
                either(variables, "NO_PROXY", "no_proxy").orElse(""))) {
            return new Repository(at, name, new Route.Direct());
        }
        Optional<String> proxy = either(variables, "HTTPS_PROXY", "https_proxy");
        if (properties.get("https.proxyHost") != null || proxy.isEmpty()) {
            return new Repository(at, name, new Route.AsJavaSays());
        }
        return switch (proxyNamed(proxy.get())) {
            case Named.At<InetSocketAddress>(InetSocketAddress through) ->
                    new Repository(at, name, new Route.Through(through));
            case Named.Not<InetSocketAddress>(Central.Failure.Misread why) ->
                    new Configured.Unusable(name,
                            new Central.Failure.Misconfigured("HTTPS_PROXY", why));
        };
    }

    /** What a setting names: the {@code T} it is read as, or why it is not one. */
    private sealed interface Named<T> {
        record At<T>(T value) implements Named<T> {}

        record Not<T>(Central.Failure.Misread why) implements Named<T> {}
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

    /**
     * Whether a request may be sent to {@code uri}: an absolute address with a host and no
     * credentials, over HTTPS, or over plain HTTP on the loopback. The one place this is decided,
     * for the repository a setting names and for every address a redirect sends a request to
     * alike. Credentials are refused because none is ever sent: an address that carries them asks
     * for something this does not do.
     */
    static boolean admits(URI uri) {
        if (!uri.isAbsolute() || uri.isOpaque() || uri.getHost() == null
                || uri.getRawUserInfo() != null) {
            return false;
        }
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

    /** The repository a setting names, or why it names none that may be asked. */
    private static Named<URI> root(String named) {
        URI uri;
        try {
            uri = new URI(named.endsWith("/") ? named : named + "/");
        } catch (URISyntaxException e) {
            return new Named.Not<>(new Central.Failure.Misread.NotAnAddress());
        }
        if (uri.getRawUserInfo() != null) {
            return credentials(uri);
        }
        if (admits(uri)) {
            return new Named.At<>(uri);
        }
        // Read as an address, and one that would be asked over plain HTTP elsewhere than this
        // machine: said as that, and shown as read.
        boolean addressed = uri.isAbsolute() && !uri.isOpaque() && uri.getHost() != null;
        return new Named.Not<>(addressed && "http".equals(uri.getScheme())
                ? new Central.Failure.Misread.Insecure(uri)
                : new Central.Failure.Misread.NotAnAddress());
    }

    /**
     * An address that carries credentials, refused as that where it has a host to show it by, and
     * as no address where it has none: what was written is never what is shown.
     */
    private static <T> Named<T> credentials(URI uri) {
        return new Named.Not<>(uri.getHost() == null ? new Central.Failure.Misread.NotAnAddress()
                : new Central.Failure.Misread.Credentials(uri));
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

    /**
     * Where {@code HTTPS_PROXY} says the proxy is, written as an {@code http://} URL or as host and
     * port. What the client cannot do with what is written is refused as such rather than dropped:
     * credentials, since it sends a proxy none when it tunnels, and any scheme but {@code http},
     * since that is the one it asks a proxy by.
     */
    private static Named<InetSocketAddress> proxyNamed(String proxy) {
        URI uri;
        try {
            uri = new URI(proxy.contains("://") ? proxy : "http://" + proxy);
        } catch (URISyntaxException e) {
            return new Named.Not<>(new Central.Failure.Misread.NotAnAddress());
        }
        if (uri.getRawUserInfo() != null) {
            return credentials(uri);
        }
        if (uri.getHost() == null) {
            return new Named.Not<>(new Central.Failure.Misread.NotAnAddress());
        }
        if (!"http".equals(uri.getScheme())) {
            return new Named.Not<>(new Central.Failure.Misread.Scheme(uri));
        }
        return new Named.At<>(InetSocketAddress.createUnresolved(uri.getHost(),
                uri.getPort() >= 0 ? uri.getPort() : 80));
    }
}
