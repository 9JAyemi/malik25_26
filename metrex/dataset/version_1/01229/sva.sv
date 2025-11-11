// SVA for adder. Bind into DUT for automatic checking.
module adder_sva #(parameter W=32)
(
  input logic              clk,
  input logic              rst,
  input logic [W-1:0]      A,
  input logic [W-1:0]      B,
  input logic [W-1:0]      Y
);
  default clocking cb @(posedge clk); endclocking

  // 1) No X/Z propagation when inputs are known
  assert property ( !$isunknown({rst,A,B}) |-> !$isunknown(Y) )
    else $error("Y has X/Z while inputs are known");

  // 2) Functional correctness (combinational, 32-bit wrap)
  assert property ( !$isunknown({rst,A,B}) |-> ( Y == (rst ? '0 : (A + B)) ) )
    else $error("Adder functional mismatch");

  // 3) Reset dominates output
  assert property ( rst |-> (Y == '0) )
    else $error("Reset active but Y != 0");

  // 4) Stability: if inputs and rst stable across cycles, Y must be stable
  assert property ( $stable({rst,A,B}) |-> $stable(Y) )
    else $error("Y changed while inputs/rst stable");

  // Functional coverage
  // Reset activity
  cover property ( rst );
  cover property ( $rose(rst) );
  cover property ( $fell(rst) );

  // Typical/edge arithmetic scenarios (when not in reset)
  cover property ( !rst && (A==0) && (B==0) && (Y==0) );
  cover property ( !rst && (A==0) && (Y==B) );
  cover property ( !rst && (B==0) && (Y==A) );
  cover property ( !rst && (A==32'hFFFF_FFFF) && (B==32'h1) && (Y==0) ); // wrap to 0
  cover property ( !rst && ((A + B) < A) ); // overflow/wraparound occurred
  cover property ( !rst && ((A + B) >= A) ); // no wrap

endmodule

// Bind into the DUT
bind adder adder_sva #(.W(32)) adder_sva_i (.*);