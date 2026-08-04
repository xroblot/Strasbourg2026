# References and resources — Introduction to Lean

*Summer school "Proof assistants and applications", Strasbourg,
31 August – 4 September 2026.*

## Before the first lecture

1. Use **Firefox**, **Chrome** or **Edge**
   (Safari is not recommended for Codespaces)
2. Create a (free) GitHub account if needed: https://github.com
3. Open the working environment:
   https://codespaces.new/xroblot/Strasbourg2026
   then click **Create codespace**
   (to find an existing Codespace: https://github.com/codespaces)
4. Wait for it to fully load (~5 minutes the first time)
5. Check: open `Part1.lean`, place the cursor on
   `#check Nat.add_comm` → a tooltip should appear

> **Be patient while Lean loads.** When you open a file, Lean
> processes it in the background; orange/yellow bars in the left
> margin (and a spinner in the status bar) mean it is still working.
> Wait until they disappear before expecting goals or tooltips —
> nothing is broken, Lean is just getting ready.

**Local installation** (alternative to Codespaces):

1. Install Lean (the `elan` toolchain manager and VS Code extension):
   https://lean-lang.org/install
2. In the terminal, clone this repository and enter it:
   ```
   git clone https://github.com/xroblot/Strasbourg2026.git
   cd Strasbourg2026
   ```
3. Download the prebuilt Mathlib cache
   (otherwise compiling Mathlib takes hours):
   ```
   lake exe cache get
   ```
4. Open the folder in VS Code and open `Part1.lean`. The first
   load takes a few minutes while Lean starts up.

**Fallback** (no installation): https://live.lean-lang.org

## At the start of the tutorial — updating the files

To be safe, always run the following command **at the very
beginning of the session** (and again later if the files are
updated): it fetches the latest version of the files. Type it in
the terminal (usually open by default at the bottom of the screen):
```
git pull
```

If the terminal is not visible, open one via the menu
**Terminal → New Terminal**, or with a keyboard shortcut:
- toggle the bottom panel (which contains the terminal):
  **Cmd + J** on macOS, **Ctrl + J** on Windows/Linux;
- or toggle the terminal directly: **Ctrl + backtick** (the
  backtick key is usually at the top-left of the keyboard, just
  below Esc) — same on all platforms.

## Official sites

- **Lean**: https://lean-lang.org
- **Lean community**: https://leanprover-community.github.io
- **Mathlib** (thematic overview):
  https://leanprover-community.github.io/mathlib-overview.html
- **Mathlib documentation**:
  https://leanprover-community.github.io/mathlib4_docs/

## Learning Lean

- **Mathematics in Lean** (reference book):
  https://leanprover-community.github.io/mathematics_in_lean/
- **Natural Number Game** (interactive game):
  https://adam.math.hhu.de/#/g/leanprover-community/NNG4

## Community

- **Zulip** (community forum): https://leanprover.zulipchat.com/
