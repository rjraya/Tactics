theory Debugger_Example
imports Pure
begin

section \<open>Minimal example\<close>

text \<open>
  \<bullet> Ensure that the Debugger panel is open

  \<bullet> Right-click on the "fun\<bullet>loop" breakpoint and enable it via context menu item
    "Toggle Breakpoint".

  \<bullet> Edit some spaces in lemma statement to re-check ML_val invocations below,
    and run into the debugger.

  \<bullet> Step through the ML source, using Debugger controls, depending on thread
    context.
\<close>

declare [[ML_debugger = true]]

ML \<open>
  fun print n s = writeln (string_of_int n ^ " " ^ s);

  fun loop n =
    if n <= 0 then n
    else
      let
       val _ = print n "a";
        val m = loop (n - 1);
        val _ = print (m + 1) "b";
      in n end;
\<close>

ML_val \<open>loop 10\<close>
ML_val \<open>loop 10\<close>
ML_val \<open>loop 10\<close>
ML_val \<open>loop 10\<close>


end