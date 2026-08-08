# 0. Getting Started

This tutorial teaches Raven through the **VS Code extension** ("Raven Verifier"), which is how
most people actually use the tool day to day. You will not need a terminal for anything in
Parts 1 through 5.

## Install {#sec:install}

1. Install [VS Code](https://code.visualstudio.com/) if you don't already have it.
2. Open the Extensions panel (`Ctrl+Shift+X` / `Cmd+Shift+X`) and search for **"Raven
   Verifier"**, published by `nyu-acsys`. Install it.
3. That's it. The extension bundles the `raven` and `z3` binaries for your platform, so there
   is nothing else to install.

(If you're following along with a local build of Raven from source instead — e.g. you're
contributing to the tool itself — see [Appendix D](../appendix/where-next.md) for how to point
the extension at a dev build via the `ravenServer.executablePath` setting. Everyone else:
ignore this and move on.)

## Your first `.rav` file {#sec:first-rav-file}

Create a new file called `scratch.rav` anywhere, and type:

```raven
proc double(x: Int) returns (r: Int)
  ensures r == 2 * x
{
  r := x + x
}
```

As soon as you save (or after you stop typing for a moment), the extension runs Raven on the
file in the background. Look at the bottom-left status bar: you should see a spinner
labeled "Raven: Verifying" briefly, then a green checkmark, **"Verification Successful."**
That checkmark is the whole point of this tool — it means Raven proved, for *every* possible
value of `x`, that `double` returns `2 * x`. Not tested for a few sample inputs: proved, for
all of them.

You can also trigger a check manually at any time with the command **"Raven: Verify File"**
(`Shift+Alt+R` on Windows/Linux, `Shift+Cmd+R` on Mac, or via the Command Palette). Use this
whenever you want to be sure you're looking at a fresh result rather than a stale one from
before your last edit.

## Breaking it on purpose {#sec:breaking-it-on-purpose}

Now change the postcondition to something false:

```raven
proc double(x: Int) returns (r: Int)
  ensures r == 3 * x
{
  r := x + x
}
```

Save. The status bar flips to a red **"Verification Failed."**, and you'll see a red squiggly
underline appear under `r == 3 * x`. Hover over it (or open the Problems panel,
`Ctrl+Shift+M` / `Cmd+Shift+M`) to read the message:

```
[Verification Error] A postcondition may not hold at this return point
```

This is worth internalizing because it's the shape of *every* failure you'll see
for the rest of this tutorial: a location (here, the closing `}`, i.e. the return point) and a
plain-English description of which proof obligation didn't go through. Red is not scary here —
it's Raven doing exactly its job, telling you precisely what it couldn't prove and where.

Fix it back to `2 * x` and confirm you get the green checkmark again before moving on.

## Two kinds of red {#sec:two-kinds-of-red}

Not all squiggles mean the same thing. Try this instead:

```raven
proc oops(x: Int) returns (r: Bool)
{
  r := x
}
```

This time the message starts with `[Type Error]`, not `[Verification Error]`, and it tells you
directly that you tried to assign an `Int` where a `Bool` was expected. A `Type Error` (or
`Syntax Error`/`Lexical Error`) means Raven couldn't even make sense of the program — nothing
was proved or disproved, because there was nothing yet to check. A `Verification Error` means
Raven understood the program perfectly well and then failed to *prove* it correct. Learning to
tell these apart at a glance (the bracketed prefix) will save you from hunting for a logic bug
in code that just has a typo.

## Debugging Corner: reading what the editor tells you

Two habits worth building right now, because every later part's "Debugging Corner" leans on
them:

1. **A failed check is often *two* linked messages, not one.** Try this:

   ```raven
   proc oops2()
     ensures false
   {
   }
   ```

   You'll see a squiggly underline at the closing `}` for the main message ("A postcondition may
   not hold at this return point"), *and* a second squiggly underline back at the `ensures
   false` clause itself, saying "This assertion may not hold." — that second one is the
   **related location**. Open the Problems panel and look at the entry to see both listed
   together; VS Code also lets you jump directly from one squiggle to the other. The first
   message tells you *what kind* of obligation failed and *where in your control flow*; the
   related location tells you *which specific piece* of a (possibly much larger) specification
   is the actual culprit. Get in the habit of reading both, not just the first line — once
   contracts grow to several `&&`-joined conjuncts, the related location is usually the only
   thing that tells you which conjunct is the problem.

2. **What Raven does *not* tell you.** It never explains *why* something is false, only *that*
   it couldn't prove it — there's no counterexample trace, no "x was 5 when this failed." As
   you'll see starting in Part 2, it also won't tell you *where* a resource went if a proof
   runs out of permission partway through. Both of these require a technique on your part, not
   a message to read; we introduce those techniques as they become relevant, rather than all
   at once here.

Finally: always re-run "Raven: Verify File" after an edit if you're not sure the squiggles
you're looking at are current. The extension re-verifies automatically on save, but there's no
harm in asking explicitly.

## What's next

[Part 1](../sequential/) starts writing actual Raven programs, restricted for now to the
purely sequential fragment of the language — no heap, no threads, just values, functions, and
control flow. If you already know a language like Dafny or Viper's sequential fragment, most
of Part 1 will feel familiar; that's deliberate.
