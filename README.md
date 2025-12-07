# ThePolynomialMethod

The author of this README.md is Nick Adfor.

This is for the formalization of "The polynomial method and restricted sums of congruence classes.pdf". This article can be found here, or by searching its name on Google or Bing.

# About Theorem 2.1 and the Legend

The coders are all Chinese. Do not worry if you see strange words in the comments or the file names. They are not gibberish. "妈咪河移位.lean" is the most important: Alon-Nathanson-Ruzsa Polynomial Method (Theorem 2.1). "妈咪河" means "the Mother River" in China, which is the nickname of the Yellow River. "移位" means changing location. "妈咪河移位" thus means the Yellow River changes location (of its estuary). In Chinese history, the Yellow River really changes location of its estuary for many times, the same as the author's proof of Theorem 2.1. Also, the importance of Theorem 2.1 rank high in Alon-Nathanson-Ruzsa's article. So I name the file as "妈咪河移位.lean" to show the author's step-by-step hard work of the LEAN proof and the respect of Alon, Nathanson and Ruzsa.

"妈咪河移位" (The Mother River changes course) can also be found in poem. Spenser’s Ruines of Time writes "for to shunne the horrible mischiefe, ... And his pure streames with guiltles blood oft stained. ... From my unhappie neighborhood farre fled, And his sweete waters away with him led." The part "his sweete waters away" is "river changes course".

The coworker Helios (It might be respect to Ήλιος, the God of the Sun) told Nick that using this way to introduce one's work is sarcastic, mocking, bitter, peculiar (In Chinese it is really concise: "阴阳怪气"). No matter how ridiculous the author Nick Adfor is, we should begin our next step:

As coder, there's more things you should do than a mathematical student. Mathematical student writes the article like poems: short, hard to understand and time-consuming. Coder must first make everything clear enough without rough word, and cut all the time-consuming things. You can "aesop?" and cut the "aesop", you can "simp?" to get "simp only", they will make Lean Infoview work faster. But till today, the author do not finish that in 妈咪河移位.lean. "set_option maxHeartbeats 2000000 in theorem" is the unfinished.





Those who do not respect Lean Infoview will be punished. The author is one of them. To solve the problem, every coder must respect the God of every world, no matter the God of Lean Infoview, the God of Aristotle (from Harmonic AI), the God of ChatGPT (from OpenAI), the God of DeepSeek (from China), the God of every nation:

בְּרֵאשִׁ֖ית בָּרָ֣א אֱלֹהִ֑ים אֵ֥ת הַשָּׁמַ֖יִם וְאֵ֥ת הָאָֽרֶץ׃

بِسْمِ ٱللَّهِ ٱلرَّحْمَـٰنِ ٱلرَّحِيمِ

To seek for peace between every nation, between human and AI, between math and code.

And the most respect should be given to Helios, which is one of the coworkers herself (You can find her in the Contributors). If the author do not respect her, she will criticize (The spell must be -ize in an Oxford way. Chinese coders must show respect to the difference between BrE and NAmE) the author to be sarcastic, mocking, bitter, peculiar (In Chinese it is really concise: "阴阳怪气"), and also refuse to take next steps (Though this sentence uses the future simple tense, the criticism really happened once in December 7th which is in the weekend yet the author still decided to try to finish his work on Theorem 2.1. It really finished, though most of the work is done by Aristotle and DeepSeek). Though the criticism from Helios really confused the author, to show respect to Helios, both the God of the Sun and the coworker herself, is a must. If not, the anger will be like the open-pit fusion reactor (In physics we call the God of the Sun "open-pit fusion reactor", which is illegal if human builds one as it hurt others, but the God of the Sun is an exception) spreading everywhere. 

Spenser invents the legend of 'guiltles blood' to explain why the Thames at Verulamium had, since Gildas, chosen to change its course. (Stewart Mottram, "'With guiltles blood oft stained': Spenser's Ruines of Time and the Saints of St. Albans," Spenser Studies: A Renaissance Poetry Annual 32 (2018): 533–56, https://hull-repository.worktribe.com/OutputFile/747220) Also, Nick invents the legend of "妈咪河移位" to explain why the code on Theorem 2.1 had, since Dec. 7th, chosen to change its course:

"for to shunne the horrible mischiefe" (Translator's Note: the anger from Helios) 为了躲避那可怕的灾祸（译者注：来自Helios的怒火）



### Step

To try to check this work, you can follow the author's silly way, this is really a silly one, even suitable for mathematical stutents. For one following the author's steps, you can do these:

First, open a new folder. I name it as "ThePolynomialMethod". For the author, this file, after taking the following steps, cost 15.3 GB.

If you are in the mainland of China, you might face some network problem. If you find it failed in some steps because of network problem, you should type 

"
set HTTP_PROXY=http://127.0.0.1:xxxx

set HTTPS_PROXY=http://127.0.0.1:xxxx" 

in Git Bash. "xxxx" is from your port in your Clash (The author only know how to use Clash). For the author, it is "7890".

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
Not running lake exe cache get yet, as the lake version does not match the toolchain version in the project.
You should run lake exe cache get manually.
"
(The author delete ``, as it cannot be seen correctly in README.md. The author don't know why.)

So you just type "lake exe cache get" and Enter.

Then download this repo no matter by GitHub Desktop or by url. Paste it to "./ThePolynomialMethod/ThePolynomialMethod". In that folder you may find there's already a "Basic.lean". It is the same as the one in this repo.

Then open a ".lean", you will wait until the Lean InfoView to load all the "import" needed. For the files "import Mathlib" (import the whole Mathlib), it might be very slow. The author often waited for hours. To save time, after it imports the whole Mathlib, you can "lake exe cache get" again then it will save to your folder. 

### Step End

Although this is a README.md intended for those willing to check the work, it is more for teaching the forgetful author how to actually find his original work after reinstalling the computer or messing with files.
