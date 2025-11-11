// SVA checker for top_module
// Bind this file to the DUT to verify combinational correctness and provide coverage.

bind top_module top_module_sva u_top_module_sva (
  .a(a),
  .b(b),
  .sum_carry_out(sum_carry_out),
  .sum(sum),
  .carry_out(carry_out),
  .sum_decimal(sum_decimal),
  // internal DUT nets
  .a_1(a_1),
  .b_1(b_1),
  .sum_half_adder(sum_half_adder),
  .carry_out_half_adder(carry_out_half_adder),
  .sum_decimal_logic_circuit(sum_decimal_logic_circuit)
);

module top_module_sva (
  input  logic [2:0] a,
  input  logic [2:0] b,
  input  logic       sum_carry_out,
  input  logic [2:0] sum,
  input  logic       carry_out,
  input  logic [5:0] sum_decimal,

  // internal DUT nets (via bind)
  input  logic [2:0] a_1,
  input  logic [2:0] b_1,
  input  logic [2:0] sum_half_adder,
  input  logic       carry_out_half_adder,
  input  logic [5:0] sum_decimal_logic_circuit
);

  // Use combinational sampling for this purely combinational DUT
  default clocking cb @(*); endclocking

  // Flag the design issue: 4-bit concat is driven into 1-bit sum_carry_out
  initial begin
    if ($bits(sum_carry_out) != 4)
      $error("sum_carry_out width (%0d) mismatches 4-bit concatenation {carry,sum}. Likely a design bug.", $bits(sum_carry_out));
  end

  // Splitter passthrough
  assert property (a_1 == a)
    else $error("splitter out_a != in_a");
  assert property (b_1 == b)
    else $error("splitter out_b != in_b");

  // Half-adder bitwise correctness
  assert property (sum_half_adder == (a_1 ^ b_1))
    else $error("half_adder sum mismatch: sum != a ^ b");
  assert property (carry_out_half_adder == (a_1[0] & b_1[0]))
    else $error("bit0 half_adder carry mismatch");
  assert property (carry_out == (a_1[2] & b_1[2]))
    else $error("bit2 half_adder carry (carry_out) mismatch");

  // Output wiring
  assert property (sum == sum_half_adder)
    else $error("sum output not driven by sum_half_adder");
  assert property (sum_decimal == sum_decimal_logic_circuit)
    else $error("sum_decimal not driven by logic_circuit out");

  // Logic circuit width-extension behavior
  assert property (sum_decimal_logic_circuit[2:0] == sum_half_adder)
    else $error("logic_circuit LSBs mismatch");
  assert property (sum_decimal_logic_circuit[5:3] == 3'b000)
    else $error("logic_circuit MSBs not zero-extended");

  // Consequence of current RTL bug: sum_carry_out equals sum[0] due to truncation
  assert property (sum_carry_out == sum_half_adder[0])
    else $error("sum_carry_out != LSB of concatenation (current implementation)");

  // End-to-end checks on ports (independent of internal nets)
  assert property (sum == (a ^ b))
    else $error("sum != a ^ b (end-to-end)");
  assert property (carry_out == (a[2] & b[2]))
    else $error("carry_out != a[2] & b[2] (end-to-end)");
  assert property (sum_decimal[2:0] == sum && sum_decimal[5:3] == 3'b000)
    else $error("sum_decimal != zero-extended sum");

  // Knownness: if inputs are 0/1, outputs must be 0/1
  assert property ((!$isunknown({a,b})) |-> (!$isunknown({sum,carry_out,sum_carry_out,sum_decimal})))
    else $error("Outputs contain X/Z while inputs are known");

  // Compact full functional coverage of inputs (all 64 combinations)
  typedef class cg_t;
    covergroup cg_ab with function sample (logic [2:0] va, logic [2:0] vb);
      coverpoint va { bins all[] = {[0:7]}; }
      coverpoint vb { bins all[] = {[0:7]}; }
      cross va, vb;
    endgroup
  endclass
  cg_t::cg_ab cg = new;

  always @* if (!$isunknown({a,b})) cg.sample(a,b);

  // Basic output activity coverage
  cover property (sum != $past(sum)) @(cb);
  cover property (carry_out != $past(carry_out)) @(cb);
  cover property (sum_decimal != $past(sum_decimal)) @(cb);

endmodule