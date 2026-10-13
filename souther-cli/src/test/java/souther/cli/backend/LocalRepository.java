package souther.cli.backend;

import com.sun.net.httpserver.HttpExchange;
import com.sun.net.httpserver.HttpServer;

import java.io.IOException;
import java.io.OutputStream;
import java.net.InetAddress;
import java.net.InetSocketAddress;
import java.net.URI;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.Executors;

/**
 * A Maven repository in Central's layout, served over HTTP on the loopback address for the length of
 * a test, which says every path it was asked for.
 */
public final class LocalRepository implements AutoCloseable {

    private static final String ROOT = "/maven2/";
    private static final String GROUP = "org/souther-lang/";

    private final HttpServer server;
    private final Map<String, byte[]> files = new ConcurrentHashMap<>();
    private final Map<String, Integer> statuses = new ConcurrentHashMap<>();
    private final Set<String> cut = ConcurrentHashMap.newKeySet();
    private final List<String> asked = new CopyOnWriteArrayList<>();
    private final CountDownLatch closed = new CountDownLatch(1);
    private final Map<String, String> redirects = new ConcurrentHashMap<>();
    private volatile long pomDelay;

    private LocalRepository(HttpServer server) {
        this.server = server;
    }

    public static LocalRepository start() throws IOException {
        HttpServer server = HttpServer.create(
                new InetSocketAddress(InetAddress.getLoopbackAddress(), 0), 0);
        LocalRepository repository = new LocalRepository(server);
        server.createContext("/", repository::serve);
        // A thread for each exchange, as a real repository answers requests at once.
        server.setExecutor(Executors.newVirtualThreadPerTaskExecutor());
        server.start();
        return repository;
    }

    /** Where the repository is, as {@code souther.repository} names it. */
    public URI uri() {
        return URI.create("http://127.0.0.1:" + server.getAddress().getPort() + ROOT);
    }

    /** Every path asked for, in the order asked. */
    public List<String> asked() {
        return List.copyOf(asked);
    }

    /** Lists {@code versions} as the artifact's. */
    public void metadata(String artifactId, String... versions) {
        StringBuilder listed = new StringBuilder();
        for (String version : versions) {
            listed.append("      <version>").append(version).append("</version>\n");
        }
        put(GROUP + artifactId + "/maven-metadata.xml", """
                <?xml version="1.0" encoding="UTF-8"?>
                <metadata>
                  <groupId>org.souther-lang</groupId>
                  <artifactId>%s</artifactId>
                  <versioning>
                    <latest>%s</latest>
                    <versions>
                %s    </versions>
                  </versioning>
                </metadata>
                """.formatted(artifactId, versions.length == 0 ? "" : versions[versions.length - 1],
                listed));
    }

    /** A pom stating the Souther it was built against. */
    public static String builtAgainst(String artifactId, String version, String southerVersion) {
        return """
                <project xmlns="http://maven.apache.org/POM/4.0.0">
                  <modelVersion>4.0.0</modelVersion>
                  <groupId>org.souther-lang</groupId>
                  <artifactId>%s</artifactId>
                  <version>%s</version>
                  <properties>
                    <souther.version>%s</souther.version>
                  </properties>
                </project>
                """.formatted(artifactId, version, southerVersion);
    }

    /** A pom stating no Souther, and naming a parent. */
    public static String inheriting(String artifactId, String version, String parentId,
                                    String parentVersion) {
        return """
                <project xmlns="http://maven.apache.org/POM/4.0.0">
                  <modelVersion>4.0.0</modelVersion>
                  <parent>
                    <groupId>org.souther-lang</groupId>
                    <artifactId>%s</artifactId>
                    <version>%s</version>
                  </parent>
                  <artifactId>%s</artifactId>
                  <properties>
                    <jackson.version>3.0.0</jackson.version>
                  </properties>
                </project>
                """.formatted(parentId, parentVersion, artifactId);
    }

    /** Serves {@code pom} as the release's pom. */
    public void pom(String artifactId, String version, String pom) {
        put(path(artifactId, version, null, "pom"), pom);
    }

    /** Serves the jar at {@code jar} as the release's jar under {@code classifier}. */
    public void jar(String artifactId, String version, String classifier, Path jar)
            throws IOException {
        files.put(path(artifactId, version, classifier, "jar"), Files.readAllBytes(jar));
    }

    /** Serves a release: its pom built against {@code southerVersion}, and its jar. */
    public void release(String artifactId, String version, String classifier,
                        String southerVersion, Path jar) throws IOException {
        pom(artifactId, version, builtAgainst(artifactId, version, southerVersion));
        jar(artifactId, version, classifier, jar);
    }

    /** Answers the release's jar with {@code status} and nothing else. */
    public void answer(String artifactId, String version, String classifier, int status) {
        statuses.put(path(artifactId, version, classifier, "jar"), status);
    }

    /**
     * Serves half the release's jar under its full length, and then nothing more until the
     * repository is closed: a connection that has stopped.
     */
    public void cut(String artifactId, String version, String classifier) {
        cut.add(path(artifactId, version, classifier, "jar"));
    }

    public void put(String path, String content) {
        files.put(path, content.getBytes(StandardCharsets.UTF_8));
    }

    public static String path(String artifactId, String version, String classifier,
                              String extension) {
        return GROUP + artifactId + "/" + version + "/" + artifactId + "-" + version
                + (classifier == null ? "" : "-" + classifier) + "." + extension;
    }

    /** Answers {@code path} by sending the request on to {@code location}. */
    public void redirect(String path, String location) {
        redirects.put(path, location);
    }

    /** Answers every pom only after {@code millis}, as a repository far away does. */
    public void slowPoms(long millis) {
        pomDelay = millis;
    }

    private void serve(HttpExchange exchange) throws IOException {
        String path = exchange.getRequestURI().getPath();
        asked.add(path);
        String file = path.startsWith(ROOT) ? path.substring(ROOT.length()) : path;
        Integer status = statuses.get(file);
        byte[] content = files.get(file);
        if (file.endsWith(".pom") && pomDelay > 0) {
            try {
                Thread.sleep(pomDelay);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
        }
        try (exchange) {
            String location = redirects.get(file);
            if (location != null) {
                exchange.getResponseHeaders().add("Location", location);
                exchange.sendResponseHeaders(302, -1);
                return;
            }
            if (status != null || content == null) {
                exchange.sendResponseHeaders(status != null ? status : 404, -1);
                return;
            }
            exchange.sendResponseHeaders(200, content.length);
            OutputStream body = exchange.getResponseBody();
            if (!cut.contains(file)) {
                body.write(content);
                body.close();
                return;
            }
            body.write(content, 0, content.length / 2);
            body.flush();
            try {
                closed.await();
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
        }
    }

    @Override
    public void close() {
        closed.countDown();
        server.stop(0);
    }
}
