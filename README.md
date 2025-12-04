# ThePolynomialMethod

The author of this README.md is Nick Adfor.

This is for the formalization of "The polynomial method and restricted sums of congruence classes.pdf". This article can be found here, or by searching its name on Google or Bing.

The coders are Chinese. Do not worry if you see strange words in the comments. They are not gibberish.

The coders accept using LLM, even rely on LLM. 

To try to check this work, you can follow the author's silly way, this is really a silly one, even suitable for mathematical stutents. For one following the author's steps, you can do these:

### Step

First, open a new folder. I name it as "ThePolynomialMethod". For the author, this file, after taking the following steps, cost 15.3 GB.

If you are in the mainland of China, you might face some network problem. If you find it failed in some steps because of network problem, you should type "set HTTP_PROXY=http://127.0.0.1:xxxx" in Git Bash. "xxxx" is from your port in your Clash (The author only know how to use Clash). For the author, it is "set HTTP_PROXY=http://127.0.0.1:7890".

Then, open the new folder in Git Bash (MINGW64). I assume that you have already install elan but do not have "v4.26.0-rc2". You can type the following:

"
elan toolchain install leanprover/lean4:v4.26.0-rc2
elan default leanprover/lean4:v4.26.0-rc2
"

and Enter.

Then, type "lake init ThePolynomialMethod" and Enter. You will sooner see a lot of files in your new folder. But they do not contain Mathlib now. 

For building the new project, you may need one of these files: "lakefile.lean" or "lakefile.toml". The author indeed does not like "lakefile.toml" (in fact he does not know how to add Mathlib in "lakefile.toml"), so he just deletes "lakefile.toml" and decides to create a new file "lakefile.lean". For one following the author's steps, you can just create a new file named "lakefile.lean" and open it and type

"
import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "v4.26.0-rc2"

package "polynomial_method" where
  -- package configuration options here

lean_lib "PolynomialMethod" where
  -- library configuration options here
"

After saving the file, you should type "lake update" in Git Bash and Enter (I assume that your Git Bash is in "ThePolynomialMethod"). It will download the following things that Mathlib depends on: mathlib(main mathematics library) plausible(statistical analysis tool) LeanSearchClient(Lean code search client) importGraph(import graph generation tool) proofwidgets(proof widgets/interactive UI) aesop(Automated Search for Proofs) Qq(quotation and anti-quotation library) batteries(additional stdlib extensions) Cli(Lean command line tools library).

After finishing, it will show you:

"
Not running `lake exe cache get` yet, as the `lake` version does not match the toolchain version in the project.
You should run `lake exe cache get` manually.
"

So you just type "lake exe cache get" and Enter.

Then download this repo no matter by GitHub Desktop or by url. Paste it to "./ThePolynomialMethod/ThePolynomialMethod". In that folder you may find there's already a "Basic.lean". It is the same as the one in this repo.

Then open a ".lean", you will wait until the Lean InfoView to load all the "import" needed. For the files "import Mathlib" (import the whole Mathlib), it might be very slow. The author often waited for hours. To save time, after it imports the whole Mathlib, you can "lake exe cache get" then it will save to your disk. 

### Step End

Although this is a README.md intended for those willing to check the work, it is more for teaching the forgetful author how to actually find his original work after reinstalling the computer or messing with files.