// SVA checker for ripple_addsub. Bind this into the DUT.
// Focus: arithmetic correctness, pipeline/feedback integrity, X-checks, and concise coverage.

module ripple_addsub_sva (
  input  logic        CLK,
  input  logic [7:0]  A,
  input  logic [7:0]  B,
  input  logic        SUB,
  input  logic [7:0]  SUM,
  input  logic        CARRY_OUT,
  input  logic [7:0]  temp_sum,   // internal
  input  logic        carry_in    // internal
);

  default clocking cb @ (posedge CLK); endclocking

  // Delay guard for $past
  logic pvalid;
  always_ff @(posedge CLK) pvalid <= 1'b1;
  default disable iff (!pvalid);

  // 9-bit reference arithmetic (uses previous-cycle inputs and carry_in)
  let add_res = {1'b0, $past(A)} + {1'b0, $past(B)} + $past(carry_in);
  let sub_res = {1'b0, $past(A)} + {1'b0, ~$past(B)} + ~($past(carry_in)); // A - B - cin

  // No-X on sampled inputs
  assert property (!$isunknown({A,B,SUB}))) else $error("A/B/SUB contain X/Z at sample");

  // Pipeline integrity
  assert property (SUM == $past(temp_sum)) else $error("SUM is not previous temp_sum");

  // Carry feedback integrity
  assert property (carry_in == $past(CARRY_OUT)) else $error("carry_in != previous CARRY_OUT");

  // Next temp_sum arithmetic correctness
  assert property (temp_sum == ($past(SUB) ? sub_res[7:0] : add_res[7:0]))
    else $error("temp_sum mismatch with A,B,SUB,carry_in");

  // Next CARRY_OUT correctness (true carry/no-borrow from 9th bit)
  assert property ((!$past(SUB)) |-> (CARRY_OUT == add_res[8]))
    else $error("CARRY_OUT (add) mismatch");
  assert property ( ($past(SUB)) |-> (CARRY_OUT == sub_res[8])) // sub_res[8]==1 => no borrow
    else $error("CARRY_OUT (sub) mismatch");

  // Basic functional covers
  cover property (!$past(SUB) && add_res[8]);           // add with carry-out
  cover property (!$past(SUB) && !add_res[8]);          // add without carry-out
  cover property ( $past(SUB) &&  sub_res[8]);          // sub, no borrow
  cover property ( $past(SUB) && !sub_res[8]);          // sub, borrow
  cover property ($changed(SUB));                       // mode toggle
  cover property ($rose(CARRY_OUT) || $fell(CARRY_OUT));// carry toggles
  cover property (SUM == 8'h00);                        // zero result observed
  cover property ((A==8'h00 && B==8'h00) || (A==8'hFF && B==8'hFF)); // corners

endmodule

// Bind example (place in a testbench or a separate bind file)
bind ripple_addsub ripple_addsub_sva u_ripple_addsub_sva (
  .CLK(CLK),
  .A(A),
  .B(B),
  .SUB(SUB),
  .SUM(SUM),
  .CARRY_OUT(CARRY_OUT),
  .temp_sum(temp_sum),
  .carry_in(carry_in)
);