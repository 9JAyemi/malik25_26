// SVA for calculator
module calculator_sva (
  input logic        clk,
  input logic        reset,
  input logic        op,       // NOTE: DUT declares op as 1-bit, but case uses 2-bit encodings
  input logic [7:0]  in1,
  input logic [7:0]  in2,
  input logic [7:0]  out
);

  // Sample post-NBA values at the clock edge
  default clocking cb @(posedge clk);
    input #1step reset, op, in1, in2, out;
  endclocking

  // Width sanity: warn if op is not 2 bits (DUT currently is 1)
  initial if ($bits(op) != 2) $warning("calculator: op is %0d bits; case uses 2-bit encodings", $bits(op));

  // Encodings (as intended by DUT case)
  localparam logic [1:0] OP_ADD = 2'b00;
  localparam logic [1:0] OP_SUB = 2'b01;
  localparam logic [1:0] OP_MUL = 2'b10;
  localparam logic [1:0] OP_DIV = 2'b11;

  // Reset behavior
  assert property (@cb reset |-> out == 8'h00);

  // Core operation checks (single-cycle)
  assert property (@cb disable iff (reset)
                   (op == OP_ADD) |-> out == (in1 + in2));

  assert property (@cb disable iff (reset)
                   (op == OP_SUB) |-> out == (in1 - in2));

  assert property (@cb disable iff (reset)
                   (op == OP_MUL) |-> out == ((in1 * in2) & 8'hFF));

  assert property (@cb disable iff (reset)
                   (op == OP_DIV && in2 != 8'h00) |-> out == (in1 / in2));

  assert property (@cb disable iff (reset)
                   (op == OP_DIV && in2 == 8'h00) |-> out == 8'h00);

  // Default case coverage/check (e.g., X/Z on op)
  assert property (@cb disable iff (reset)
                   !(op inside {OP_ADD, OP_SUB, OP_MUL, OP_DIV}) |-> out == 8'h00);

  // Output should be 2-state when not in reset
  assert property (@cb disable iff (reset) !$isunknown(out));

  // Coverage: ops and corner cases
  cover property (@cb reset ##1 !reset);

  cover property (@cb disable iff (reset) op == OP_ADD);
  cover property (@cb disable iff (reset) op == OP_SUB);
  cover property (@cb disable iff (reset) op == OP_MUL);
  cover property (@cb disable iff (reset) op == OP_DIV && in2 != 8'h00);
  cover property (@cb disable iff (reset) op == OP_DIV && in2 == 8'h00);
  cover property (@cb disable iff (reset) !(op inside {OP_ADD, OP_SUB, OP_MUL, OP_DIV}));

  // Overflow/underflow scenarios
  cover property (@cb disable iff (reset) (op == OP_ADD) && ((in1 + in2) < in1));       // add overflow
  cover property (@cb disable iff (reset) (op == OP_SUB) && (in1 < in2));               // sub underflow
  cover property (@cb disable iff (reset) (op == OP_MUL) && ((in1 * in2) > 8'hFF));     // mul overflow

endmodule

// Bind into DUT
bind calculator calculator_sva sva (.*);