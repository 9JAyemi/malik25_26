// SVA for bitwise_operations_with_adder
// Bind these to your DUT and provide a clock/reset for sampling.

module bitwise_operations_with_adder_sva (
  input logic               clk,
  input logic               rst_n,

  input logic [31:0]        a,
  input logic [31:0]        b,
  input logic [1:0]         operation_select,
  input logic [4:0]         shift_amount,
  input logic [15:0]        adder_input,
  input logic               select,

  input logic [31:0]        bitwise_result,
  input logic [31:0]        adder_result
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // X/Z robustness: when driving inputs are known, outputs must be known
  assert property (!$isunknown({a,b,operation_select,shift_amount,select})) |-> !$isunknown(bitwise_result))
    else $error("bitwise_result has X/Z with known controls/operands");

  assert property (!$isunknown({a,b,adder_input})) |-> !$isunknown(adder_result))
    else $error("adder_result has X/Z with known operands");

  // Adder correctness: adder_result == (a & b) + zero-extended adder_input
  assert property ( adder_result == ((a & b) + {16'b0, adder_input}) )
    else $error("adder_result mismatch");

  // Select override: when select=1, output must be AND regardless of opcode
  assert property ( select |-> (bitwise_result == (a & b)) )
    else $error("select override mismatch");

  // Opcode decode when not overridden
  assert property ( (!select && operation_select==2'b00) |-> (bitwise_result == (a & b)) )
    else $error("AND decode mismatch");
  assert property ( (!select && operation_select==2'b01) |-> (bitwise_result == (a | b)) )
    else $error("OR decode mismatch");
  assert property ( (!select && operation_select==2'b10) |-> (bitwise_result == (a ^ b)) )
    else $error("XOR decode mismatch");
  assert property ( (!select && operation_select==2'b11) |-> (bitwise_result == (a << shift_amount)) )
    else $error("SLL decode mismatch");

  // Functional consistency: adder ignores select/opcode (already implied by adder check)
  assert property ( (select || !select) |-> (adder_result == ((a & b) + {16'b0, adder_input})) );

  // Targeted functional coverage
  // Each opcode exercised without override
  cover property (!select && operation_select==2'b00);
  cover property (!select && operation_select==2'b01);
  cover property (!select && operation_select==2'b10);
  cover property (!select && operation_select==2'b11);

  // Override path taken for each opcode value
  cover property ( select && operation_select==2'b00 );
  cover property ( select && operation_select==2'b01 );
  cover property ( select && operation_select==2'b10 );
  cover property ( select && operation_select==2'b11 );

  // Shift edge cases
  cover property ( !select && operation_select==2'b11 && shift_amount==5'd0 );
  cover property ( !select && operation_select==2'b11 && shift_amount==5'd31 );

  // Adder edge cases: zero, max, and wraparound
  cover property ( ((a & b)==32'h0000_0000) && (adder_input==16'h0000) );
  cover property ( ((a & b)==32'hFFFF_FFFF) && (adder_input==16'hFFFF) );
  cover property ( (((a & b) + {16'b0, adder_input}) < (a & b)) ); // 32-bit wrap
endmodule

// Example bind (provide clk/rst_n from your TB/env):
// bind bitwise_operations_with_adder bitwise_operations_with_adder_sva u_sva (
//   .clk(clk), .rst_n(rst_n),
//   .a(a), .b(b), .operation_select(operation_select),
//   .shift_amount(shift_amount), .adder_input(adder_input),
//   .select(select), .bitwise_result(bitwise_result), .adder_result(adder_result)
// );