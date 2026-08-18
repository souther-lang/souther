# ADR-0103: A decomposition and its inverse are present together

Status: Accepted. Widens ADR-0040 (the boundary map-key set) and ADR-0047 (the ordered
primitives): both reason about a temporal set of two and there are four.

## Context

Issue #623 reported that a `Date` could not be built from parts a model already holds. A model of
Japan's high-cost medical expense benefit holds the month of treatment as `{ 年: Int, 月: Int }` —
a month, not a day — and the rule it has to state names *the first of the month following the month
of treatment*. There was no expression for that date, so what got written compared month ordinals
and a `25` a reader has to re-derive.

The issue said there was no way in. Measured, that was not true. The arithmetic takes arbitrary
`Int`s, and a literal may be written anywhere, so three additions from a written anchor reach any
date:

```souther
let ofParts (y: Int, m: Int, d: Int): Date =
    Date("0001-01-01")
        |> Date.addYears(y - 1)
        |> Date.addMonths(m - 1)
        |> Date.addDays(d - 1)
```

`ofParts(2026, 7, 1)` is the 1st of July. `ofParts(2026, 2, 30)` is the **2nd of March**, and
`ofParts(2026, 13, 1)` is the 1st of January 2027. The route exists and cannot refuse: a model that
asks for a day the calendar does not have is handed a day it does, and nothing downstream can tell
that from the day it asked for.

So the defect was not a missing entrance. `[#temporal-literal]` said "a computed date comes from the
boundary or from the arithmetic below", which is exactly this route — the specification named it and
was right about it. What the library had was `Date -> (Int, Int, Int)`, three total readers, and
nothing in the other direction that could say *no*. The projection was there and the injection was
not, so the two directions disagreed about whether a date is its parts.

The same shape sat one level along. `DateTime` had `toDate` and no `toTime`, so its date part was
readable by composition and its time of day was readable not at all. And it carried nanoseconds —
`java.time.LocalDateTime` unadorned — which no model could read, write, or compare against anything
it could name. A value crossed the boundary, survived equality, changed what was encoded, and was
invisible to every operation the language had.

## Decision

**A type's decomposition and its inverse are present together, and the inverse refuses rather than
normalises.**

Three things follow from it, and one type is admitted by it.

`Date.fromParts(year, month, day) : Date | NotADate` and
`Time.fromParts(hour, minute, second) : Time | NotATime` read parts back into a value. Each is the
inverse of the readers beside it —

    Date.fromParts(Date.year(d), Date.month(d), Date.day(d)) == d
    Time.fromParts(Time.hour(t), Time.minute(t), Time.second(t)) == t

— and neither normalises. February the 30th is `NotADate`, not the 2nd of March. This is where a
refusal belongs once the parts are values rather than text: a written date is refused at compile
time because the text is there to be read, and parts are refused at the position that built them,
which is the split `String.toInt` already makes.

`Time` becomes a primitive, and `DateTime` is a `Date` and a `Time` — `toDate` / `toTime` /
`fromDateAndTime`. The last cannot fail, and that is the point of the shape: whatever could have
been wrong about the parts was refused where the `Date` and the `Time` were built, so joining them
has nothing left to check and no case to write an arm for. Partiality sits on the two small types
and not on the one composed from them.

`Time` and `DateTime` are held to the second — a `Date` is a day and has no time of day to hold a
finer reading. Text finer than the second is refused where it is
written (E1322) and at the boundary that carried it (a decode failure at that path), rather than
being rounded on the way in. Text naming a leap second is refused the same way and for a sharper
reason: `Instant.parse` answers `23:59:59` for `23:59:60`, so admitting it would put a *different*
moment in the model with nothing saying so.

An offset is not refused at a boundary. `09:30:00+09:00` and `00:30:00Z` are one moment and either
determines it, so reading the first loses nothing; what source refuses is the *spelling*, because a
written value is written the way the value is written back. An offset is a displacement from UTC and
a zone is a place with rules about when its offset changes; this language names neither, and saying
so keeps the door open for either to be added later as its own type. `Instant` is admitted as the type that keeps a sub-second reading and
an absolute moment, and it has **no calendar decomposition**: naming its year or its hour needs a
zone, the language names no zone, so there is nothing to read a part with and nothing to build one
from parts either. The two directions are absent together, which is what keeps `Instant` from being
the hole `Date` was.

`souther.instant` is empty, and that is a smaller claim than the one above. What the zone rules out
is the calendar; elapsed time between two instants, or a shift along the timeline, needs no zone and
is not ruled out by anything here. None is added because nothing asks for one yet, and adding an
operation of that kind later is a library growing rather than this decision being reversed. A model holds one, compares two, keys a `Map` by one, and declares a behavior with
no implementation to get a `DateTime` back — the same way it gets the current time.

## Consequences

`BOUNDARY_VERSION` moves from 13 to 14. The contract narrowed: a jar built before this accepts
`"2026-07-01T09:30:45.123"` at a `DateTime` field that a jar built now refuses, and a caller trusting
the older number would be told a value crosses that no longer does. It widened too — `Time` and
`Instant` are shapes an older compiler has no type for.

**The resolution of a local temporal is one second, chosen and not inherited.** A business rule is
stated in dates, hours and minutes, and one second is the resolution this language gives a local
temporal. That is a decision about resolution and not about which type a sub-second reading belongs
to: a deadline at 09:00:00.500 is a wall-clock value and would want a finer `Time`, not an `Instant`
— reaching for `Instant` there would ask a model for a date and a zone it does not have. Should a
sub-second local semantics be wanted, what is reconsidered is this resolution. Fixing the
resolution is also what gives `Time` and `DateTime` a smallest step, which is what lets a boundary
row be asked for beside a line on one — a dense carrier can only report *not derivable* there.

That the old `DateTime` carried nanoseconds no model could read is the evidence that nothing is lost
by choosing this, not the reason for choosing it: "there was no reader, so remove the values" is a
bad general rule — it would take a scale off a `Decimal`. The claim here is the other one, that a
second is the right resolution for a local temporal in this language. Should a millisecond ever be
wanted, the question to argue is whether that resolution changes, not whether a gap is being fixed.

Nothing in the corpus or the examples wrote a sub-second temporal. One test did —
`OneCarrierTableAnswersForEveryOrderedTypeTest`, whose moments were a nanosecond apart to stand for
adjacent ones — and it is now written a second apart, which is what adjacent means. That the rest
broke nothing is not why the narrowing is right: nanoseconds were unreadable, so the capability
being removed was one no model could use.

Two primitives cost more than two enum constants. `DATETIME` was named at 37 places across 18 files,
and about six of them were `type == Type.DATETIME` comparisons or hand-written name lists that
adding a constant does not force anyone to update. Those were rewritten as switches over
`Type.Prim`, so the next primitive stops the build at each place that has to answer for it rather
than being silently answered "no". Two of them were switch *statements* over `LeafScalar`, which
javac does not hold to covering an enum — `Time` and `Instant` would have had no decoder emitted at
all and compiled clean. `ATemporalIsBuiltFromThePartsAModelHoldsTest` walks `LeafScalar.values()`
and sends one value of each primitive across a boundary and back, so a primitive left out of a codec
fails a test rather than passing one that named the types it knew about.

`fromParts` answers one case for a calendar that has no such day and for a year a date cannot hold,
as `NotANumber` answers one case for text that is no number and for a number too large to carry.
What a caller does about either is the same: the parts it had do not name a date.

Holding a `DateTime` to the second gives it a smallest step, which it did not have, and that
settles a decision ADR-0090 recorded as nobody's. `Carrier.MOMENT` was dense because "a date-time
has no smallest step this language names"; it steps by a second now, so a strict bound on a
`DateTime` sharpens onto the second beside it and the row beside a line is asked for, as it is on a
day count. `BoundaryDomain.MOMENT` names that neighbour instead of answering *not derivable*, and
the counts on the carrier are whole.

`Time` and `Instant` carried nothing when this was written, which is the same question read the
other way: each had a count that would embed — a second of the day, a nanosecond from an epoch —
and a carrier owes a conversion both ways, which neither had been given. Two units in one carrier
is what `DATE` and `MOMENT` are separate to avoid, so neither could borrow `MOMENT`'s either.
Superseded on the first half in #846: the two conversions are written and each of the two has a
carrier of its own, which is what the second half said it would have to be.

## The rule, and how far it reaches

**A lossless decomposition and its inverse are present together.** `(year, month, day)` is all of a
`Date` and `(hour, minute, second)` is all of a `Time`, so each pair is a claim that the type *is*
what the readers answer — and a claim with no way back is the defect #623 found: reachable by a route
that cannot refuse, or not reachable at all.

It does not reach a reader that answers part of a value. `Date.dayOfWeek` and `Date.dayOfYear` are
derived observations, and `Instant` would owe nothing for an epoch reader either: none of them
determines the value, so none of them claims the type is made of it and none demands an inverse. The
test is whether the readers together name the value, not whether a reader exists.

Nor does it reach `Instant`, for the other reason. Its parts are not lossy — they are absent, since
naming one needs a zone. The two directions are missing together, which is the state this rule wants
and not the one it exists to correct.
