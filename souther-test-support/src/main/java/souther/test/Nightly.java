package souther.test;

import org.junit.jupiter.api.Tag;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * A test left out of the run a change waits on, and asked once a night instead.
 *
 * <p>What it costs is the whole of the reason. A test is here because paying for it on every change
 * buys less than the wait costs, which is a fact about this machine and this suite rather than about
 * what the test claims — so it is written beside the claim and not derived from it, and a test that
 * becomes cheap loses this and keeps what it says.
 *
 * <p>Cost alone is not enough. A test is here when no cheaper way to ask the same question was
 * found and when what it finds is as well found by the morning as by the change that caused it, and
 * the class says both beside the claim. A test whose claim a change needs at once stays in the run a
 * change waits on, and is made cheaper.
 *
 * <p>The tag is what surefire reads, and it is spelled here once. A plain run leaves the tag out
 * through {@code test.excluded.groups}; a run that means to ask these empties that property.
 *
 * <p><b>At the top of a file and not inside one.</b> A tag at a class covers the {@code @Nested}
 * classes in it, so this would also be legal at one — and the readers of it would then disagree,
 * since {@code bin/CoverageSubsumption} reads a file of test source as one class. What is deferred
 * is a whole file, and {@code WhatIsDeferredToTheNightlyIsAWholeTestClassTest} is what asks for it.
 */
@Target(ElementType.TYPE)
@Retention(RetentionPolicy.RUNTIME)
@Tag(Nightly.TAG)
public @interface Nightly {

    /** How the tag is spelled where a build names it. */
    String TAG = "nightly";
}
