package souther.test;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.fail;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Optional;
import java.util.function.Supplier;
import java.util.stream.Stream;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import org.junit.platform.engine.TestDescriptor;
import org.junit.platform.engine.TestExecutionResult;
import org.junit.platform.engine.TestSource;
import org.junit.platform.engine.UniqueId;
import org.junit.platform.engine.support.descriptor.AbstractTestDescriptor;
import org.junit.platform.engine.support.descriptor.ClassSource;
import org.junit.platform.engine.support.descriptor.MethodSource;
import org.junit.platform.launcher.TestIdentifier;

/**
 * A class's file holds what the agent recorded between the previous boundary and its own, and
 * nothing is written for a method, and nothing at all in a run that did not ask.
 */
class WhatAClassCoveredIsCutAtItsOwnBoundaryTest {

    /** Each take is one distinct record, so a file can be read back to the take it was. */
    private static final class Takes implements Supplier<byte[]> {
        private final Deque<byte[]> served = new ArrayDeque<>();
        private int count;

        @Override
        public byte[] get() {
            count++;
            byte[] record = ("take-" + count).getBytes();
            served.add(record);
            return record;
        }
    }

    private static TestIdentifier identifierOf(String name, TestSource source) {
        TestDescriptor descriptor = new AbstractTestDescriptor(
                UniqueId.root("test", name), name, source) {
            @Override
            public Type getType() {
                return Type.CONTAINER;
            }
        };
        return TestIdentifier.from(descriptor);
    }

    @Test
    void eachClassIsWrittenUnderItsNameWithTheTakeAtItsBoundary(@TempDir Path dir)
            throws IOException {
        Takes takes = new Takes();
        CoverageByClass listener = new CoverageByClass(Optional.of(dir), takes);

        listener.testPlanExecutionStarted(null);
        listener.executionFinished(
                identifierOf("a", ClassSource.from("souther.example.ATest")),
                TestExecutionResult.successful());
        listener.executionFinished(
                identifierOf("b", ClassSource.from("souther.example.BTest")),
                TestExecutionResult.successful());

        byte[] discovery = takes.served.pollFirst();
        assertArrayEquals(takes.served.pollFirst(),
                Files.readAllBytes(dir.resolve("souther.example.ATest.exec")));
        assertArrayEquals(takes.served.pollFirst(),
                Files.readAllBytes(dir.resolve("souther.example.BTest.exec")));
        assertEquals("take-1", new String(discovery),
                "what ran before the first class is taken so that it belongs to no class");
        try (Stream<Path> files = Files.list(dir)) {
            assertEquals(2, files.count());
        }
    }

    @Test
    void aMethodBoundaryWritesNothingAndTakesNothing(@TempDir Path dir) throws IOException {
        Takes takes = new Takes();
        CoverageByClass listener = new CoverageByClass(Optional.of(dir), takes);

        listener.executionFinished(
                identifierOf("m", MethodSource.from("souther.example.ATest", "answers")),
                TestExecutionResult.successful());

        assertEquals(0, takes.count);
        try (Stream<Path> files = Files.list(dir)) {
            assertEquals(0, files.count());
        }
    }

    @Test
    void aRunThatDidNotAskNeverReachesForTheAgent() {
        CoverageByClass listener = new CoverageByClass(
                Optional.empty(), () -> fail("a plain run must not take the agent's data"));

        listener.testPlanExecutionStarted(null);
        listener.executionFinished(
                identifierOf("a", ClassSource.from("souther.example.ATest")),
                TestExecutionResult.successful());

        assertFalse(Files.exists(Path.of("souther.example.ATest.exec")));
    }
}
