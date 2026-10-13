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
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.Executors;

/**
 * A Maven repository in Central's layout, served over HTTP on the loopback address for the length of
 * a test, which says every path it was asked for.
 *
 * <p>A path is served in one way, which {@link Serving} names, and is held back for a while first
 * where the test says so: what is served and when it begins are the two things a test varies, and
 * each path has one of each.
 */
public final class LocalRepository implements AutoCloseable {

    private static final String ROOT = "/maven2/";
    private static final String GROUP = "org/souther-lang/";

    /** How a path is answered. */
    private sealed interface Serving {

        /** The file, whole, or a 404 where there is none. */
        record Whole() implements Serving {}

        /** This status, and nothing else. */
        record Status(int status) implements Serving {}

        /** The request sent on to {@code location}. */
        record Redirect(String location) implements Serving {}

        /** The file, a {@code pieces}th at a time, {@code millis} apart. */
        record Trickle(int pieces, long millis) implements Serving {}

        /** Half the file under its full length, then nothing until the repository is closed. */
        record Cut() implements Serving {}

        /** The answer begun, and nothing of the file until the repository is closed. */
        record Silent() implements Serving {}
    }

    private final HttpServer server;
    private final Map<String, byte[]> files = new ConcurrentHashMap<>();
    private final Map<String, Serving> serving = new ConcurrentHashMap<>();
    private final Map<String, Long> heldBack = new ConcurrentHashMap<>();
    private final List<String> asked = new CopyOnWriteArrayList<>();
    private final CountDownLatch closed = new CountDownLatch(1);
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
        serving.put(path(artifactId, version, classifier, "jar"), new Serving.Status(status));
    }

    /**
     * Serves half the release's jar under its full length, and then nothing more until the
     * repository is closed: a connection that has stopped.
     */
    public void cut(String artifactId, String version, String classifier) {
        serving.put(path(artifactId, version, classifier, "jar"), new Serving.Cut());
    }

    /** Begins the answer for {@code path} and sends nothing of it until the repository is closed. */
    public void silence(String path) {
        serving.put(path, new Serving.Silent());
    }

    /** Serves {@code path} a {@code pieces}th at a time, {@code millis} apart, all of it in the end. */
    public void trickle(String path, int pieces, long millis) {
        serving.put(path, new Serving.Trickle(pieces, millis));
    }

    /** Answers {@code path} by sending the request on to {@code location}. */
    public void redirect(String path, String location) {
        serving.put(path, new Serving.Redirect(location));
    }

    /** Begins the answer for {@code path}, however it is served, only after {@code millis}. */
    public void holdBack(String path, long millis) {
        heldBack.put(path, millis);
    }

    /** Begins the answer for every pom only after {@code millis}, as a repository far away does. */
    public void slowPoms(long millis) {
        pomDelay = millis;
    }

    public void put(String path, String content) {
        files.put(path, content.getBytes(StandardCharsets.UTF_8));
    }

    public static String path(String artifactId, String version, String classifier,
                              String extension) {
        return GROUP + artifactId + "/" + version + "/" + artifactId + "-" + version
                + (classifier == null ? "" : "-" + classifier) + "." + extension;
    }

    private void serve(HttpExchange exchange) throws IOException {
        String path = exchange.getRequestURI().getPath();
        asked.add(path);
        String file = path.startsWith(ROOT) ? path.substring(ROOT.length()) : path;
        pause(heldBack.getOrDefault(file, file.endsWith(".pom") ? pomDelay : 0));
        byte[] content = files.get(file);
        try (exchange) {
            switch (serving.getOrDefault(file, new Serving.Whole())) {
                case Serving.Status status -> exchange.sendResponseHeaders(status.status(), -1);
                case Serving.Redirect redirect -> {
                    exchange.getResponseHeaders().add("Location", redirect.location());
                    exchange.sendResponseHeaders(302, -1);
                }
                case Serving.Whole _ -> {
                    if (content == null) {
                        exchange.sendResponseHeaders(404, -1);
                    } else {
                        exchange.sendResponseHeaders(200, content.length);
                        try (OutputStream body = exchange.getResponseBody()) {
                            body.write(content);
                        }
                    }
                }
                case Serving.Trickle trickle -> {
                    exchange.sendResponseHeaders(200, content.length);
                    try (OutputStream body = exchange.getResponseBody()) {
                        int piece = (int) Math.ceil(content.length / (double) trickle.pieces());
                        for (int from = 0; from < content.length; from += piece) {
                            body.write(content, from, Math.min(piece, content.length - from));
                            body.flush();
                            pause(trickle.millis());
                        }
                    }
                }
                case Serving.Cut _ -> {
                    exchange.sendResponseHeaders(200, content.length);
                    OutputStream body = exchange.getResponseBody();
                    body.write(content, 0, content.length / 2);
                    body.flush();
                    awaitClose();
                }
                case Serving.Silent _ -> {
                    exchange.sendResponseHeaders(200, content.length);
                    exchange.getResponseBody().flush();
                    awaitClose();
                }
            }
        }
    }

    private void awaitClose() {
        try {
            closed.await();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
    }

    private static void pause(long millis) {
        if (millis <= 0) {
            return;
        }
        try {
            Thread.sleep(millis);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
    }

    @Override
    public void close() {
        closed.countDown();
        server.stop(0);
    }
}
