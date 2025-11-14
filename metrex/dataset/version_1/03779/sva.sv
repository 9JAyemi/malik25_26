// SVA for top_module (binds into the DUT and taps internal nets via .*)

module top_module_sva(
  input a,
  input b,
  input sel_xor,
  input sel_mux,
  input xor_out,
  input mux_out,
  input out_always
);

  // No X/Z on any important signal
  assert property (@(a or b or sel_xor or sel_mux or xor_out or mux_out or out_always)
                   !$isunknown({a,b,sel_xor,sel_mux,xor_out,mux_out,out_always}));

  // Leaf correctness
  assert property (@(a or b) $changed({a,b}) |-> ##0 (xor_out == (a ^ b)));
  assert property (@(a or b or sel_mux) $changed({a,b,sel_mux}) |-> ##0 (mux_out == (sel_mux ? b : a)));

  // Top-level select function
  assert property (@(a or b or sel_xor or sel_mux)
                   $changed({a,b,sel_xor,sel_mux}) |-> ##0
                   (out_always ==
                     ((sel_xor & ~sel_mux) ? xor_out :
                      (sel_mux & ~sel_xor) ? mux_out :
                      (sel_mux & sel_xor)  ? 1'b1     : 1'b0)));

  // Coverage: exercise all select branches and outcomes
  cover property (@(a or b or sel_xor or sel_mux)
                  $changed({a,b,sel_xor,sel_mux}) ##0 (sel_xor && !sel_mux && out_always==0));
  cover property (@(a or b or sel_xor or sel_mux)
                  $changed({a,b,sel_xor,sel_mux}) ##0 (sel_xor && !sel_mux && out_always==1));

  cover property (@(a or b or sel_xor or sel_mux)
                  $changed({a,b,sel_xor,sel_mux}) ##0 (sel_mux && !sel_xor && out_always==0));
  cover property (@(a or b or sel_xor or sel_mux)
                  $changed({a,b,sel_xor,sel_mux}) ##0 (sel_mux && !sel_xor && out_always==1));

  cover property (@(a or b or sel_xor or sel_mux)
                  $changed({a,b,sel_xor,sel_mux}) ##0 ( sel_xor &&  sel_mux && out_always==1));
  cover property (@(a or b or sel_xor or sel_mux)
                  $changed({a,b,sel_xor,sel_mux}) ##0 (!sel_xor && !sel_mux && out_always==0));

endmodule

bind top_module top_module_sva i_top_module_sva (.*);