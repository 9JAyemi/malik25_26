// SVA for top_module and its sub-blocks (bindable). Assumes a TB clock/reset.
// Focused, concise, and complete for functional correctness and key coverage.

module top_sva (
  input  logic        clk,
  input  logic        rst_n,

  // top_module I/Os
  input  logic [3:0]  A,
  input  logic [3:0]  B,
  input  logic        select,
  input  logic        subtract,
  input  logic        eq,
  input  logic        gt,
  input  logic [3:0]  result,

  // internal nets of top_module
  input  logic [3:0]  adder_out,
  input  logic [3:0]  comparator_out,
  input  logic [3:0]  final_result
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Basic X-check: known inputs imply known outputs
  assert property (!$isunknown({A,B,select,subtract}) |-> !$isunknown({eq,gt,result,adder_out,comparator_out,final_result}));

  // Adder/Subtractor behavior (mod-16)
  assert property ( adder_out == ( (subtract ? (A - B) : (A + B)) & 4'hF ) );

  // Comparator flags correctness
  assert property ( eq == (A == B) );
  assert property ( gt == (A >  B) );
  assert property ( !(eq && gt) ); // mutually exclusive

  // Comparator result encoding (zero-extended {gt,eq})
  assert property ( comparator_out == {2'b00, gt, eq} );

  // Mux/select correctness
  assert property ( final_result == (select ? comparator_out : adder_out) );
  assert property ( result == final_result );

  // Coverage: exercise key modes and boundaries
  cover property ( subtract==1'b0 );                    // add mode
  cover property ( subtract==1'b1 );                    // subtract mode
  cover property ( select==1'b0 );                      // select adder
  cover property ( select==1'b1 );                      // select comparator
  cover property ( (A+B) >= 5'd16 && !subtract );       // add overflow/wrap
  cover property ( (A < B) &&  subtract );              // subtract underflow/wrap
  cover property ( A == B && eq && !gt );               // equality case
  cover property ( A >  B && gt && !eq );               // greater-than case
  cover property ( A <  B && !gt && !eq );              // less-than case
  cover property ( select && (comparator_out != adder_out) ); // mux picks comparator when paths differ
  cover property ( !select && (comparator_out != adder_out) );// mux picks adder when paths differ

endmodule

// Example bind (hook clk/rst_n from your TB):
// bind top_module top_sva u_top_sva (
//   .clk        (tb_clk),
//   .rst_n      (tb_rst_n),
//   .A          (A),
//   .B          (B),
//   .select     (select),
//   .subtract   (subtract),
//   .eq         (eq),
//   .gt         (gt),
//   .result     (result),
//   .adder_out  (adder_out),
//   .comparator_out (comparator_out),
//   .final_result   (final_result)
// );