package souther.cli.init;

import org.junit.jupiter.api.Test;
import souther.compiler.fmt.Formatter;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The {@code .sou} that {@code init} writes is one {@code souther fmt --check} passes.
 *
 * <p>Asked as {@code fmt --check} asks it: the text is its own formatting. The build is not among the
 * cases, because {@link Templates#sourcesOf} does not read it — a Maven, a Gradle and an existing
 * project are handed the same source.
 */
class WhatInitWritesIsAlreadyInTheFormFmtWritesTest {

    @Test
    void everyModelThisCommandWritesIsInTheFormFmtWrites() {
        for (Model model : Model.values()) {
            Project project = new Project(new Coordinate("com.example", "hello"),
                    "com.example.hello", model, BuildSystem.MAVEN, "9.9.9");
            String written = Templates.sourcesOf(project).getFirst().content();
            assertEquals(Formatter.format(written), written,
                    () -> model + " is not in the form fmt writes");
        }
    }
}
