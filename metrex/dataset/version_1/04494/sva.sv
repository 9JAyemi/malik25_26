// SVA for adder_4bit
module adder_4bit_sva (
  input logic [3:0] A,
  input logic [3:0] B,
  input logic       CIN,
  input logic       CLK,
  input logic       RST,
  input logic [3:0] SUM,
  input logic       COUT
);

  // Clocking block
  default clocking cb @(posedge CLK); endclocking

  // Arithmetic correctness and 1-cycle latency
  // After any cycle with RST=1, on the next clock {COUT,SUM} must equal A+B+CIN of the prior cycle.
  ap_math: assert property (cb disable iff (!RST)
    (RST && $past(RST)) |-> {COUT,SUM} == $past(A + B + CIN)
  );

  // Outputs known when not in reset
  ap_known: assert property (cb disable iff (!RST)
    !$isunknown({SUM,COUT})
  );

  // Asynchronous reset drives outputs to zero immediately
  ap_rst_immediate: assert property (@(negedge RST)
    (SUM == 4'b0) && (COUT == 1'b0)
  );

  // While reset is low, outputs remain zero on every clock
  ap_rst_hold: assert property (cb
    !RST |-> (SUM == 4'b0 && COUT == 1'b0)
  );

  // -------------- Functional coverage --------------

  // Reset asserted/deasserted
  cp_rst_assert:   cover property (@(negedge RST) 1);
  cp_rst_release:  cover property (@(posedge RST) 1);

  // Cover both CIN values
  cp_cin0: cover property (cb CIN == 1'b0);
  cp_cin1: cover property (cb CIN == 1'b1);

  // Cover both COUT results
  cp_cout0: cover property (cb disable iff (!RST) COUT == 1'b0);
  cp_cout1: cover property (cb disable iff (!RST) COUT == 1'b1);

  // Extremes of 5-bit result space
  cp_min_sum: cover property (cb disable iff (!RST) {COUT,SUM} == 5'd0);
  cp_max_sum: cover property (cb disable iff (!RST) {COUT,SUM} == 5'd31);

  // Observe a correct arithmetic update event
  cp_math_hit: cover property (cb disable iff (!RST)
    (RST && $past(RST)) && ({COUT,SUM} == $past(A + B + CIN))
  );

endmodule

// Bind into DUT
bind adder_4bit adder_4bit_sva sva_i (
  .A(A), .B(B), .CIN(CIN), .CLK(CLK), .RST(RST), .SUM(SUM), .COUT(COUT)
);