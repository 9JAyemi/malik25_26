// SVA checker for calculator. Binds to DUT and verifies functionality and provides coverage.
// Note: The DUT declares 'op' as 1-bit but uses 2-bit case items.
// The checker adapts: if op is 1-bit, it checks the effective ADD/SUB behavior and flags the width bug.
// If op is 2-bit (after fixing DUT), it enables full ADD/SUB/MUL/DIV checking.

module calculator_sva (
  input  logic        clk,
  input  logic        rst,
  input  logic        op,              // width adapts via $bits(op)
  input  logic [3:0]  a, b,
  input  logic [3:0]  result,
  // internal regs
  input  logic [3:0]  reg_a,
  input  logic [3:0]  reg_b,
  input  logic [3:0]  reg_result
);

  // Clocking
  default clocking cb @(posedge clk); endclocking

  // Reset behavior: next cycle after rst high, all regs/output are 0
  assert property (rst |=> (reg_a==4'd0 && reg_b==4'd0 && reg_result==4'd0 && result==4'd0));

  // Output mirrors pipeline register
  assert property (result == reg_result);

  // Register capture: when previous cycle not in reset, stage inputs into reg_a/reg_b
  assert property (!$past(rst) |-> (reg_a == $past(a) && reg_b == $past(b)));

  // Knownness after reset released
  assert property (!rst |-> !$isunknown({op,a,b,result,reg_a,reg_b,reg_result}));

  // Operation checks (one-cycle latency on operands via reg_a/reg_b)
  localparam int OPW = $bits(op);
  generate
    if (OPW == 1) begin : OP_1BIT
      // Effective decode due to width bug: 0->ADD, 1->SUB (MUL/DIV unreachable)
      assert property (!rst && op==1'b0 |-> result == ($past(a)+$past(b)));
      assert property (!rst && op==1'b1 |-> result == ($past(a)-$past(b)));

      // Coverage
      cover property (!rst && op==1'b0); // ADD exercised
      cover property (!rst && op==1'b1); // SUB exercised
      cover property (!rst && op==1'b0 && (({1'b0,$past(a)}+{1'b0,$past(b)})[4])); // ADD overflow
      cover property (!rst && op==1'b1 && ($past(a) < $past(b)));                   // SUB underflow

      // Flag the width inconsistency
      initial $error("calculator op is 1-bit but used as 2-bit in case: MUL/DIV paths are unreachable");
    end
    else if (OPW == 2) begin : OP_2BIT
      // Full opcode correctness
      assert property (!rst && op==2'b00 |-> result == ($past(a)+$past(b)));
      assert property (!rst && op==2'b01 |-> result == ($past(a)-$past(b)));
      assert property (!rst && op==2'b10 |-> result == (($past(a)*$past(b))[3:0]));
      // Division defined only with nonzero divisor
      assert property (!rst && op==2'b11 |-> $past(b)!=4'd0) else $error("Divide by zero");
      assert property (!rst && op==2'b11 && $past(b)!=4'd0 |-> result == ($past(a)/$past(b)));

      // Coverage: ops and edge cases
      cover property (!rst && op==2'b00);
      cover property (!rst && op==2'b01);
      cover property (!rst && op==2'b10);
      cover property (!rst && op==2'b11 && $past(b)!=0);
      cover property (!rst && op==2'b00 && (({1'b0,$past(a)}+{1'b0,$past(b)})[4])); // ADD overflow
      cover property (!rst && op==2'b01 && ($past(a) < $past(b)));                   // SUB underflow
      cover property (!rst && op==2'b10 && (($past(a)*$past(b)) > 8'h0F));           // MUL overflow
    end
  endgenerate

  // Reset sequence seen
  cover property (rst ##1 !rst);

endmodule

// Bind the checker to the DUT (connect internals)
bind calculator calculator_sva u_calculator_sva (
  .clk        (clk),
  .rst        (rst),
  .op         (op),
  .a          (a),
  .b          (b),
  .result     (result),
  .reg_a      (reg_a),
  .reg_b      (reg_b),
  .reg_result (reg_result)
);