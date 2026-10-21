package souther.cli.backend;

import java.io.IOException;
import java.net.InetSocketAddress;
import java.net.Proxy;
import java.net.ProxySelector;
import java.net.SocketAddress;
import java.net.URI;
import java.util.HashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.StringJoiner;
import java.util.regex.Pattern;

/**
 * The proxy Java's networking properties name for a request, read from the properties a run is
 * given and not from the JVM's.
 *
 * <p>Read the way the JDK's own selector reads them for the two schemes a repository is asked by,
 * so a run given this process's properties is sent where the JVM's selector would send it. The
 * host is {@code <scheme>.proxyHost}, or {@code proxyHost} where that is not set; the port is
 * {@code <scheme>.proxyPort}, then {@code proxyPort}, then the scheme's own. A host
 * {@code http.nonProxyHosts} names is asked directly, by HTTPS as well as by HTTP: the list is
 * patterns split at {@code |}, each matching the whole host and taking {@code *} at either end, and
 * the loopback names are added to a list that names something and stand alone where no list is set.
 * A SOCKS proxy is not named here, because the client sends a request through no proxy but an
 * HTTP one.
 *
 * <p>Where no host is named and {@code java.net.useSystemProxies} asks for the system's proxies,
 * the system is asked through the JVM's selector. What the system names is not a property, and
 * the JVM reads it only where the JVM itself was started asking for it.
 */
final class ProxyProperties extends ProxySelector {

    /** What {@code http.nonProxyHosts} holds where it is not set, and is added to where it is. */
    private static final String LOOPBACK = "localhost|127.*|[::1]|0.0.0.0|[::0]";

    private static final Map<String, Integer> SCHEMES = Map.of("http", 80, "https", 443);

    /** The proxy each scheme names, for the schemes that name one. */
    private final Map<String, InetSocketAddress> named = new HashMap<>();

    /** The hosts asked directly, or null where no host is. */
    private final Pattern direct;

    private final boolean socks;

    private final boolean system;

    ProxyProperties(Map<String, String> properties) {
        for (Map.Entry<String, Integer> scheme : SCHEMES.entrySet()) {
            // The port is looked for under the prefix the host was found under first, and under
            // the other one after.
            List<String> prefixes = List.of(scheme.getKey() + ".proxy", "proxy");
            for (int at = 0; at < prefixes.size(); at++) {
                String host = set(properties, prefixes.get(at) + "Host");
                if (host == null) {
                    continue;
                }
                int port = port(properties, prefixes.get(at) + "Port");
                if (port == 0) {
                    port = port(properties, prefixes.get(1 - at) + "Port");
                }
                named.put(scheme.getKey(), InetSocketAddress.createUnresolved(host,
                        port == 0 ? scheme.getValue() : port));
                break;
            }
        }
        String listed = properties.get("http.nonProxyHosts");
        direct = pattern(listed == null ? LOOPBACK
                : listed.isEmpty() ? "" : listed + "|" + LOOPBACK);
        // A SOCKS proxy named stands in the system's place, and is one the client sends nothing
        // through.
        socks = set(properties, "socksProxyHost") != null;
        system = Boolean.parseBoolean(properties.get("java.net.useSystemProxies"));
    }

    @Override
    public List<Proxy> select(URI uri) {
        InetSocketAddress proxy = named.get(uri.getScheme().toLowerCase(Locale.ROOT));
        if (proxy == null) {
            return system && !socks ? ProxySelector.getDefault().select(uri)
                    : List.of(Proxy.NO_PROXY);
        }
        String host = uri.getHost().toLowerCase(Locale.ROOT);
        if (direct != null && direct.matcher(host).matches()) {
            return List.of(Proxy.NO_PROXY);
        }
        return List.of(new Proxy(Proxy.Type.HTTP, proxy));
    }

    /** Nothing is remembered of a proxy that could not be reached: the next request is sent to it
     *  again, as it is by the JVM's selector. */
    @Override
    public void connectFailed(URI uri, SocketAddress proxy, IOException failure) {
    }

    /** The property, where it is set to something. */
    private static String set(Map<String, String> properties, String name) {
        String value = properties.get(name);
        return value == null || value.isEmpty() ? null : value;
    }

    /** The port the property names, or 0 where it names none. */
    private static int port(Map<String, String> properties, String name) {
        String value = properties.get(name);
        if (value == null) {
            return 0;
        }
        try {
            return Integer.decode(value);
        } catch (NumberFormatException _) {
            return 0;
        }
    }

    /** The hosts {@code list} names as one pattern, or null where it names none. */
    private static Pattern pattern(String list) {
        StringJoiner alternatives = new StringJoiner("|");
        boolean any = false;
        for (String each : list.split("\\|")) {
            if (each.isEmpty()) {
                continue;
            }
            any = true;
            String host = each.toLowerCase(Locale.ROOT);
            boolean leading = host.startsWith("*");
            boolean trailing = host.length() > 1 && host.endsWith("*");
            String middle = host.equals("*") ? ""
                    : host.substring(leading ? 1 : 0, host.length() - (trailing ? 1 : 0));
            alternatives.add((leading ? ".*" : "") + Pattern.quote(middle)
                    + (trailing ? ".*" : ""));
        }
        return any ? Pattern.compile(alternatives.toString()) : null;
    }
}
