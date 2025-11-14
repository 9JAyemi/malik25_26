// SVA for counter. Bind this to the DUT.
module counter_sva (
  input logic        CLK,
  input logic        RST,
  input logic        UP_DOWN,
  input logic [3:0]  Q
);
  default clocking cb @(posedge CLK); endclocking

  // Basic X checks (clean operation domain)
  assert property (!RST |-> !$isunknown(UP_DOWN)) else $error("UP_DOWN X/Z when not in reset");
  assert property (!RST |-> !$isunknown(Q))       else $error("Q X/Z when not in reset");

  // Reset behavior
  // Next cycle after reset high -> Q must be 0
  assert property (RST |=> Q==4'h0) else $error("Q not 0 on cycle after reset");
  // While reset is held, Q must read as 0 (from the prior cycle's assignment)
  assert property ($past(RST) && RST |-> Q==4'h0) else $error("Q not held at 0 during reset");

  // Counting behavior (mod-16)
  assert property ($past(!RST) && $past(UP_DOWN)  |-> Q == ($past(Q)+4'd1)[3:0])
    else $error("Up-count next-state mismatch");
  assert property ($past(!RST) && !$past(UP_DOWN) |-> Q == ($past(Q)-4'd1)[3:0])
    else $error("Down-count next-state mismatch");

  // Optional: step magnitude is always +/-1 when not in reset
  assert property ($past(!RST) |-> (((Q - $past(Q)) & 4'hF) inside {4'h1,4'hF}))
    else $error("Q changed by more than 1 step");

  // Coverage
  cover property (RST ##1 !RST); // observe a reset release
  cover property (!RST && UP_DOWN && Q==4'hF ##1 !RST && Q==4'h0); // wrap-up F->0
  cover property (!RST && !UP_DOWN && Q==4'h0 ##1 !RST && Q==4'hF); // wrap-down 0->F
  cover property (!RST && UP_DOWN ##1 !RST && !UP_DOWN); // both directions exercised
endmodule

bind counter counter_sva u_counter_sva (.*);