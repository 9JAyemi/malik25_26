// SVA for d_ff, xor_gate, and_gate, and top_module
// Bind these checkers to the DUT for concise, high-quality checking and useful coverage.

////////////////////////////////////////
// d_ff checker
////////////////////////////////////////
module dff_sva(input logic clk, input logic d, input logic q);
  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1;

  default clocking @(posedge clk); endclocking

  // q must equal previous-cycle d
  property q_follows_d;
    past_valid |-> (q == $past(d));
  endproperty
  assert property (q_follows_d) else $error("d_ff: q != $past(d)");

  // Coverage: d and q toggle
  cover property (past_valid && (d != $past(d)));
  cover property (past_valid && (q != $past(q)));
endmodule
bind d_ff dff_sva dff_chk(.clk(clk), .d(d), .q(q));

////////////////////////////////////////
// xor_gate checker (event-driven)
////////////////////////////////////////
module comb_xor_sva(input logic [2:0] a, b, input logic [2:0] out_xor);
  property xor_is_correct;
    @(a or b or out_xor) out_xor == (a ^ b);
  endproperty
  assert property (xor_is_correct) else $error("xor_gate: out_xor != a ^ b");

  // Coverage: any nonzero XOR
  cover property (@(a or b) ((a ^ b) != 3'b000));
endmodule
bind xor_gate comb_xor_sva xor_chk(.a(a), .b(b), .out_xor(out_xor));

////////////////////////////////////////
// and_gate checker (event-driven)
////////////////////////////////////////
module comb_and_sva(input logic [2:0] a, b, input logic [2:0] out_and);
  property and_is_correct;
    @(a or b or out_and) out_and == (a & b);
  endproperty
  assert property (and_is_correct) else $error("and_gate: out_and != a & b");

  // Coverage: any AND bit is 1
  cover property (@(a or b) (|(a & b)));
endmodule
bind and_gate comb_and_sva and_chk(.a(a), .b(b), .out_and(out_and));

////////////////////////////////////////
// top_module checker
////////////////////////////////////////
module top_module_sva(
  input  logic        clk, select,
  input  logic [2:0]  a, b,
  input  logic [2:0]  xor_out, and_out,
  input  logic [2:0]  a_not, b_not,
  input  logic [2:0]  out_xor_bitwise,
  input  logic        out_and_logical,
  input  logic [5:0]  out_not
);
  default clocking @(posedge clk); endclocking

  // Select=1: outputs reflect combinational results and registered NOTs
  property p_sel1;
    select |-> (
      (out_xor_bitwise == (a ^ b)) &&
      (out_and_logical == (a[0] & b[0])) &&
      (out_not[2:0] == b_not) &&
      (out_not[5:3] == a_not)
    );
  endproperty
  assert property (p_sel1) else $error("top_module: select=1 output mismatch");

  // Select=0: outputs forced low; note out_not becomes 6'b0 due to truncation
  property p_sel0;
    !select |-> (
      (out_xor_bitwise == 3'b000) &&
      (out_and_logical == 1'b0) &&
      (out_not == 6'b000000)
    );
  endproperty
  assert property (p_sel0) else $error("top_module: select=0 output mismatch");

  // Basic X-check when select is known
  assert property (!$isunknown(select) |-> !$isunknown({out_xor_bitwise,out_and_logical,out_not}))
    else $error("top_module: X/Z on outputs when select known");

  // Coverage: exercise both select branches and useful data cases
  cover property (select);
  cover property (!select);
  cover property (select ##1 !select);
  cover property (!select ##1 select);
  cover property (select && ((a ^ b) != 3'b000));
  cover property (select && (a[0] & b[0]));
  cover property (select && (out_not != 6'b000000));
endmodule

bind top_module top_module_sva top_chk(
  .clk(clk), .select(select),
  .a(a), .b(b),
  .xor_out(xor_out), .and_out(and_out),
  .a_not(a_not), .b_not(b_not),
  .out_xor_bitwise(out_xor_bitwise),
  .out_and_logical(out_and_logical),
  .out_not(out_not)
);