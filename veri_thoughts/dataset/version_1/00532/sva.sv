// SVA for adder_subtractor
// Bind this module to the DUT: bind adder_subtractor adder_subtractor_sva sva(.clk(clk), .rst(rst), .A(A), .B(B), .sub(sub), .out(out), .cout(cout));

module adder_subtractor_sva (
  input logic        clk,
  input logic        rst,
  input logic [3:0]  A,
  input logic [3:0]  B,
  input logic        sub,
  input logic [3:0]  out,
  input logic        cout
);

  default clocking cb @(posedge clk); endclocking

  // Track past-valid for safe $past() usage
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Effective operands per DUT logic (5-bit to capture carry)
  let A_eff5 = {1'b0, (sub ? ~A : A)};
  let B_eff5 = {1'b0, (sub ? (~B + 4'd1) : B)};
  let nxt5   = A_eff5 + B_eff5 + $past(cout);

  // Basic sanity: no X/Z on sampled IOs
  assert property (!$isunknown({A,B,sub,rst}))) else $error("X/Z on inputs at clk edge");
  assert property (!$isunknown({out,cout})))   else $error("X/Z on outputs at clk edge");

  // Synchronous reset behavior
  assert property (rst |-> (out == 4'd0 && cout == 1'b0))
    else $error("Reset failed to clear outputs");

  // Functional next-state check (matches DUT sequential add with feedback carry)
  assert property (disable iff (!past_valid) (!rst) |-> {cout,out} == nxt5)
    else $error("Next-state mismatch: {{cout,out}} != A_eff5 + B_eff5 + $past(cout)");

  // Outputs should only change on clk posedge (check at negedge for stability)
  assert property (@(negedge clk) $stable({out,cout}))
    else $error("Outputs changed between clock edges");

  // Coverage

  // Exercise reset then deassert
  cover property (rst ##1 !rst);

  // Exercise addition path (sub=0), no carry and carry-out
  cover property (disable iff (!past_valid) !rst && !sub && cout);
  cover property (disable iff (!past_valid) !rst && !sub && !cout);

  // Exercise subtraction path (sub=1), observe both cout states
  cover property (disable iff (!past_valid) !rst && sub && cout);
  cover property (disable iff (!past_valid) !rst && sub && !cout);

  // Exercise carry feedback in use ($past(cout)=1 influences next sum)
  cover property (disable iff (!past_valid) !rst && $past(cout) && ({cout,out} == (A_eff5 + B_eff5 + 5'd1)));

  // Toggle sub between cycles
  cover property (disable iff (!past_valid) !rst && !$past(sub) && sub);
  cover property (disable iff (!past_valid) !rst &&  $past(sub) && !sub);

  // Boundary operands
  cover property (disable iff (!past_valid) !rst && (A==4'hF) && (B==4'hF) && !sub);
  cover property (disable iff (!past_valid) !rst && (A==4'h0) && (B==4'h0) && sub);

endmodule