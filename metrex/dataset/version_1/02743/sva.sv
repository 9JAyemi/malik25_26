// SVA for dff_async_reset (synchronous reset despite name)
module dff_async_reset_sva (
  input logic CLK,
  input logic D,
  input logic RST,
  input logic Q
);
  default clocking @(posedge CLK); endclocking
  default disable iff ($isunknown({CLK,RST,D}));

  // Single concise next-state check (covers reset priority and data capture)
  // Q at this tick equals (prior RST ? 0 : prior D)
  assert property ( $past(1'b1) |-> (Q == ($past(RST) ? 1'b0 : $past(D))) )
    else $error("DFF next-state mismatch: Q != (RST?0:D) from previous cycle");

  // Output should not go X when prior inputs are known
  assert property ( $past(1'b1) && !$isunknown({$past(RST),$past(D)}) |-> !$isunknown(Q) )
    else $error("Q is X with known prior inputs");

  // Q must only change on CLK posedge (no asynchronous glitches)
  always @(Q) assert ($rose(CLK))
    else $error("Q changed without CLK posedge");

  // Coverage: exercise reset path and data capture of 0/1
  cover property ( $past(RST) && (Q==0) );               // reset took effect
  cover property ( $past(!RST) &&  $past(D) && (Q==1) ); // captured 1
  cover property ( $past(!RST) && !$past(D) && (Q==0) ); // captured 0
endmodule

// Bind to DUT
bind dff_async_reset dff_async_reset_sva sva_i (.CLK(CLK), .D(D), .RST(RST), .Q(Q));