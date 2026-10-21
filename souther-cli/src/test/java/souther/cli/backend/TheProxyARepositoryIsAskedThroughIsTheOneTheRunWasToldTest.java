package souther.cli.backend;

import org.junit.jupiter.api.Test;

import java.net.InetSocketAddress;
import java.net.Proxy;
import java.net.ProxySelector;
import java.net.URI;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * The proxy the repository's client sends a request through is the one the properties the run was
 * given name, and not the one the JVM running it was started with.
 *
 * <p>Which repository is asked and how it is reached are decided from the same settings, so the
 * client is asked here what it would send a request through: its own selector where it has one, and
 * the JVM's where it has none, which is how the client itself chooses. Nothing in this JVM names a
 * proxy, so a client that fell back on the JVM's would answer every case below with none.
 */
class TheProxyARepositoryIsAskedThroughIsTheOneTheRunWasToldTest {

    private static final URI CENTRAL = Repository.MAVEN_CENTRAL.resolve("souther/x.jar");

    private static Proxy http(String host, int port) {
        return new Proxy(Proxy.Type.HTTP, InetSocketAddress.createUnresolved(host, port));
    }

    /** What the client of the repository these settings name sends a request for {@code uri}
     *  through. */
    private static List<Proxy> sentThrough(Map<String, String> variables,
                                           Map<String, String> properties, URI uri) {
        Repository repository = assertInstanceOf(Repository.class,
                Repository.configured(variables, properties));
        return repository.client().proxy().orElseGet(ProxySelector::getDefault).select(uri);
    }

    @Test
    void theHostAndPortThePropertiesNameAreTheProxy() {
        assertEquals(List.of(http("proxy.example", 3128)), sentThrough(Map.of(),
                Map.of("https.proxyHost", "proxy.example", "https.proxyPort", "3128"), CENTRAL));
    }

    @Test
    void aPortNotNamedIsTheSchemesOwn() {
        assertEquals(List.of(http("proxy.example", 443)), sentThrough(Map.of(),
                Map.of("https.proxyHost", "proxy.example"), CENTRAL));
    }

    /** {@code proxyHost} and {@code proxyPort} name the proxy of every scheme that names none of
     *  its own, as they do to Java's own selector. */
    @Test
    void theSchemeLessPropertiesStandWhereTheSchemesAreNotSet() {
        assertEquals(List.of(http("proxy.example", 8080)), sentThrough(Map.of(),
                Map.of("proxyHost", "proxy.example", "proxyPort", "8080"), CENTRAL));
    }

    /** {@code http.nonProxyHosts} is the list HTTPS is read by as well, and the loopback names are
     *  on it whatever else it holds. */
    @Test
    void aHostTheNonProxyHostsNameIsAskedDirectly() {
        Map<String, String> properties = Map.of("https.proxyHost", "proxy.example",
                "http.nonProxyHosts", "*.internal");

        assertEquals(List.of(Proxy.NO_PROXY), sentThrough(Map.of(), properties,
                URI.create("https://repo.internal/maven2/x.jar")));
        assertEquals(List.of(Proxy.NO_PROXY), sentThrough(Map.of(), properties,
                URI.create("https://localhost/maven2/x.jar")));
        assertEquals(List.of(http("proxy.example", 443)), sentThrough(Map.of(), properties,
                CENTRAL));
    }

    /** The loopback names are added to a list that names a host, and stand alone where no list is
     *  set; a list set to nothing names nothing. */
    @Test
    void anEmptyListNamesNoHostNotEvenTheLoopback() {
        assertEquals(List.of(http("proxy.example", 443)), sentThrough(Map.of(),
                Map.of("https.proxyHost", "proxy.example", "http.nonProxyHosts", ""),
                URI.create("https://localhost/maven2/x.jar")));
    }

    /** The property stands over {@code HTTPS_PROXY}, so the variable is not the proxy where both
     *  are set; where only the variable is, it is. */
    @Test
    void thePropertyStandsOverTheVariable() {
        assertEquals(List.of(http("proxy.example", 3128)), sentThrough(
                Map.of("HTTPS_PROXY", "http://elsewhere.example:8080"),
                Map.of("https.proxyHost", "proxy.example", "https.proxyPort", "3128"), CENTRAL));
        assertEquals(List.of(http("elsewhere.example", 8080)), sentThrough(
                Map.of("HTTPS_PROXY", "http://elsewhere.example:8080"), Map.of(), CENTRAL));
    }

    @Test
    void nothingNamedIsNoProxy() {
        assertEquals(List.of(Proxy.NO_PROXY), sentThrough(Map.of(), Map.of(), CENTRAL));
    }
}
