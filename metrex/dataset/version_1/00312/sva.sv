// SVA checker for calculator
module calculator_checker (
  input logic        clk,
  input logic [7:0]  A,
  input logic [7:0]  B,
  input logic [1:0]  op,
  input logic [7:0]  result,
  input logic        overflow,
  input logic        underflow
);
  // Clocking/control
  default clocking cb @(posedge clk); endclocking
  logic past_valid; initial past_valid = 1'b0; always @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Opcode aliases
  localparam logic [1:0] OP_ADD = 2'b00,
                         OP_SUB = 2'b01,
                         OP_MUL = 2'b10,
                         OP_DIV = 2'b11;

  // Expected results/flags from past inputs
  let add8     = $past(A) + $past(B);
  let add_ovf  = ($past(A)[7] == $past(B)[7]) && (add8[7] != $past(A)[7]); // signed overflow

  let sub8     = $past(A) - $past(B);
  let sub_ovf  = ($past(A)[7] != $past(B)[7]) && (sub8[7] != $past(A)[7]); // signed overflow
  let sub_udf  = ($past(A)[7] == 1'b0) && ($past(B)[7] == 1'b0) && ($past(A) < $past(B)); // unsigned borrow when both positive

  let mul16    = $past(A) * $past(B);
  let mul_lo8  = mul16[7:0];
  let mul_ovf  = (mul16[15:8] != 8'h00);

  let div0     = ($past(B) == 8'h00);
  let div_q    = div0 ? 8'h00 : ($past(A) / $past(B));

  // Functional correctness per opcode (registered, 1-cycle latency)
  assert property ( ( $past(op) == OP_ADD ) |-> (result == add8   && overflow == add_ovf && underflow == 1'b0) )
    else $error("ADD mismatch");

  assert property ( ( $past(op) == OP_SUB ) |-> (result == sub8   && overflow == sub_ovf && underflow == sub_udf) )
    else $error("SUB mismatch");

  assert property ( ( $past(op) == OP_MUL ) |-> (result == mul_lo8 && overflow == mul_ovf && underflow == 1'b0) )
    else $error("MUL mismatch");

  assert property ( ( $past(op) == OP_DIV ) |-> (result == div_q   && overflow == 1'b0    && underflow == div0) )
    else $error("DIV mismatch");

  // Flags sanity
  assert property ( !(overflow && underflow) ) else $error("Both overflow and underflow asserted");

  // No X/Z on observable outputs after first cycle
  assert property ( !$isunknown({result, overflow, underflow}) ) else $error("X/Z detected on outputs");

  // Basic opcode coverage
  cover property ( $past(op) == OP_ADD );
  cover property ( $past(op) == OP_SUB );
  cover property ( $past(op) == OP_MUL );
  cover property ( $past(op) == OP_DIV );

  // Interesting scenario coverage
  cover property ( ($past(op) == OP_ADD) && add_ovf );
  cover property ( ($past(op) == OP_SUB) && sub_ovf );
  cover property ( ($past(op) == OP_SUB) && sub_udf );
  cover property ( ($past(op) == OP_MUL) && mul_ovf );
  cover property ( ($past(op) == OP_DIV) &&  div0    );
  cover property ( ($past(op) == OP_DIV) && !div0    );
endmodule

// Bind into DUT
bind calculator calculator_checker chk (
  .clk(clk),
  .A(A),
  .B(B),
  .op(op),
  .result(result),
  .overflow(overflow),
  .underflow(underflow)
);