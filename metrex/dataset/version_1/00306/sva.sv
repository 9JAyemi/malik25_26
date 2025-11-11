// SVA for subtractor: saturating subtract (Y=0 when A<B, else Y=A-B on next cycle)

module subtractor_sva #(parameter WIDTH=8)
(
  input logic                 clk,
  input logic [WIDTH-1:0]     A,
  input logic [WIDTH-1:0]     B,
  input logic [WIDTH-1:0]     Y
);

  // track first valid cycle for $past()
  bit started;
  initial started = 1'b0;
  always_ff @(posedge clk) started <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!started);

  // X/Z checks
  a_inputs_known: assert property ( !$isunknown(A) && !$isunknown(B) )
    else $error("subtractor: A/B contain X/Z");

  a_output_known: assert property ( !$isunknown(Y) )
    else $error("subtractor: Y contains X/Z");

  // Functional correctness (one-cycle latency)
  a_functional: assert property (
    Y == ( ($past(A) < $past(B)) ? '0 : ($past(A) - $past(B)) )
  ) else $error("subtractor: Y mismatch: A=%0d B=%0d Y=%0d exp=%0d",
                $past(A), $past(B), Y,
                (($past(A) < $past(B)) ? '0 : ($past(A) - $past(B))));

  // Optional consistency: unchanged inputs => unchanged output
  a_stable_when_inputs_stable: assert property (
    $stable(A) && $stable(B) |-> Y == $past(Y)
  ) else $error("subtractor: Y changed while A,B stable");

  // Functional coverage
  c_sat:     cover property ( (A <  B) |=> (Y == '0) );
  c_normal:  cover property ( (A >= B) |=> (Y == $past(A) - $past(B)) );
  c_equal:   cover property ( (A == B) |=> (Y == '0) );
  c_b_zero:  cover property ( (B == '0) |=> (Y == $past(A)) );

endmodule

// Bind into DUT
bind subtractor subtractor_sva #(.WIDTH(8)) u_subtractor_sva (.clk(clk), .A(A), .B(B), .Y(Y));