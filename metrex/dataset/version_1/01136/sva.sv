// SVA checker for mux_2to1
module mux_2to1_sva (
  input logic D0, D1, S, RST, CLK,
  input logic Y
);
  default clocking cb @(posedge CLK); endclocking

  // past-valid for safe $past() and X checks
  logic past_valid;
  initial past_valid = 0;
  always @(posedge CLK) past_valid <= 1;

  // Core functional check: 1-cycle registered mux with sync reset
  // Y(n) == (RST(n-1) ? 0 : (S(n-1) ? D1(n-1) : D0(n-1)))
  assert property (disable iff (!past_valid)
                   Y == ($past(RST) ? 1'b0
                                    : ($past(S) ? $past(D1) : $past(D0))))
    else $error("mux_2to1: next-state mismatch");

  // Sanity/X checks on sampled values
  assert property (disable iff (!past_valid) !$isunknown(RST))
    else $error("mux_2to1: RST is X/Z at clock edge");
  assert property (disable iff (!past_valid) !RST |-> !$isunknown({S,D0,D1}))
    else $error("mux_2to1: S/D inputs X/Z when RST=0");
  assert property (disable iff (!past_valid) !$isunknown(Y))
    else $error("mux_2to1: Y is X/Z");

  // Minimal yet meaningful coverage
  cover property (disable iff (!past_valid) RST ##1 (Y==1'b0));               // reset forces 0
  cover property (disable iff (!past_valid) !RST && !S ##1 (Y==D0));          // D0 path
  cover property (disable iff (!past_valid) !RST &&  S ##1 (Y==D1));          // D1 path
  cover property (disable iff (!past_valid)
                  !RST && !S ##1 (Y==D0) ##1 !RST && S ##1 (Y==D1));          // select switch exercised
  cover property (disable iff (!past_valid) !RST && !S && $changed(D0) ##1 $changed(Y)); // D0->Y propagation
  cover property (disable iff (!past_valid) !RST &&  S && $changed(D1) ##1 $changed(Y)); // D1->Y propagation
endmodule

// Bind into the DUT
bind mux_2to1 mux_2to1_sva u_mux_2to1_sva (
  .D0(D0), .D1(D1), .S(S), .RST(RST), .CLK(CLK), .Y(Y)
);