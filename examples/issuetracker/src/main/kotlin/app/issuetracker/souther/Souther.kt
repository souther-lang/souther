// The Kotlin side of the Souther boundary: three extensions and one exception, none of which name a
// domain type. It is the Kotlin counterpart of the souther-clj library under examples/account — small
// enough to read in one sitting, and written to be lifted out of this example unchanged.
//
// Kotlin needs less glue than Clojure did. A generated output union is a Java `sealed` interface, so
// `when` over it is exhaustive with no macro to check it; a generated data's read accessors are typed,
// so no reflective unwrapping is needed. What is left is the three places where Souther's shapes and
// Kotlin's differ: raoh's Result vs Kotlin's exceptions-at-the-boundary, souther's Option vs Kotlin's
// nullability, and Behavior.apply vs a function call.
package app.issuetracker.souther

import net.unit8.raoh.Issues
import net.unit8.raoh.decode.Decoder
import souther.runtime.Behavior
import souther.runtime.Option

/**
 * A decoder rejected outside input. This is not a domain case — the domain never sees the value — so it
 * is an exception the boundary maps to 400 (see BoundaryErrors), the same treatment Spring gives its
 * own binding failures. The issues are Raoh's, with their paths and codes intact.
 */
class DecodeFailed(val issues: Issues) : RuntimeException(issues.toString())

/**
 * Decodes from the root path, or fails the request. Construction is the guarded direction (spec 2.1):
 * this is the only way the boundary turns an outside value into a domain value, and the data's
 * invariants are checked on the way through.
 */
fun <I, T> Decoder<I, T>.decodeOrFail(input: I): T = decode(input).orElseThrow(::DecodeFailed)

/** Souther's `T?` read as Kotlin's `T?`, so the rest of the boundary uses `?.` and `?:`. */
fun <T> Option<T>.orNull(): T? = when (this) {
    is Option.Some<T> -> value
    is Option.None<T> -> null
}

/** Calls a bound behavior as a function: `attachLabel(request)` rather than `attachLabel.apply(request)`. */
operator fun <I, O> Behavior<I, O>.invoke(input: I): O = apply(input)
