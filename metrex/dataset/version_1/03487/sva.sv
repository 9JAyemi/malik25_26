// SVA for dff_async_reset
module dff_async_reset_sva (input logic D, CLK, RESET, Q);

  // 1) Asynchronous reset forces Q low immediately
  assert property (@(posedge RESET) ##0 (Q == 1'b0))
    else $error("Q not forced low immediately on async RESET");

  // 2) While RESET is high, Q must be 0 at every qualifying edge
  assert property (@(posedge CLK or posedge RESET) RESET |-> (Q == 1'b0))
    else $error("Q not held low while RESET asserted");

  // 3) Synchronous capture on CLK when not in reset
  assert property (@(posedge CLK) (!RESET && $past(!RESET)) |-> (Q == $past(D)))
    else $error("Q did not capture D on CLK rising edge");

  // 4) No change on RESET deassert edge itself (Q stays 0)
  assert property (@(negedge RESET) ##0 (Q == 1'b0))
    else $error("Q changed on RESET deassert edge");

  // 5) Basic X/Z checks at control edges
  assert property (@(posedge CLK or posedge RESET) !$isunknown({D, CLK, RESET}))
    else $error("X/Z on inputs at control edge");
  assert property (@(posedge CLK or posedge RESET) !$isunknown(Q))
    else $error("Q is X/Z at control edge");

  // COV: async reset behavior exercised
  cover property (@(posedge RESET) ##0 (Q == 1'b0));
  // COV: capture 1 after reset release
  cover property (@(posedge CLK)
                  (!RESET && $past(!RESET) && $past(D)==1'b1 && Q==1'b1));
  // COV: capture 0 after reset release
  cover property (@(posedge CLK)
                  (!RESET && $past(!RESET) && $past(D)==1'b0 && Q==1'b0));
  // COV: Q toggles both ways via clocked captures
  cover property (@(posedge CLK) (!RESET && $past(!RESET) && $past(D)==0 && Q==0) ##1
                  (!RESET && $past(!RESET) && $past(D)==1 && Q==1));

endmodule

// Bind into DUT
bind dff_async_reset dff_async_reset_sva sva_i(.D(D), .CLK(CLK), .RESET(RESET), .Q(Q));