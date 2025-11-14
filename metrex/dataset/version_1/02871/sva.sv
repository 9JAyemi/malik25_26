// SVA for calculator
// Bind this file to the DUT. Focused, concise checks + coverage.

module calculator_sva #(
  parameter NUM_OPERATIONS = 4
) (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic [1:0] OP,
  input  logic [3:0] RESULT
);

  localparam logic [1:0] OP_ADD = 2'b00;
  localparam logic [1:0] OP_SUB = 2'b01;
  localparam logic [1:0] OP_MUL = 2'b10;
  localparam logic [1:0] OP_DIV = 2'b11;

  function automatic bit known4 (logic [3:0] v); return !$isunknown(v); endfunction
  function automatic bit known2 (logic [1:0] v); return !$isunknown(v); endfunction

  wire inputs_known = known4(A) && known4(B) && known2(OP);

  // OP validity
  assert property (@(A or B or OP) known2(OP) |-> (OP < NUM_OPERATIONS));

  // Correctness per operation (sample after delta to avoid race with comb logic)
  assert property (@(A or B or OP)
    inputs_known && (OP==OP_ADD) |-> ##0 (RESULT === (A + B))
  );

  assert property (@(A or B or OP)
    inputs_known && (OP==OP_SUB) |-> ##0 (RESULT === (A - B))
  );

  assert property (@(A or B or OP)
    inputs_known && (OP==OP_MUL) |-> ##0 (RESULT === (A * B)[3:0])
  );

  assert property (@(A or B or OP)
    inputs_known && (OP==OP_DIV) && (B!=0) |-> ##0 (RESULT === (A / B))
  );

  // Divide-by-zero should yield unknown result
  assert property (@(A or B or OP)
    inputs_known && (OP==OP_DIV) && (B==0) |-> ##0 $isunknown(RESULT)
  );

  // When inputs known and not div-by-zero, output must be known
  assert property (@(A or B or OP)
    inputs_known && !(OP==OP_DIV && B==0) |-> ##0 !$isunknown(RESULT)
  );

  // Functional coverage (event-driven, zero-delay safe where needed)
  cover property (@(A or B or OP) (OP==OP_ADD));
  cover property (@(A or B or OP) (OP==OP_SUB));
  cover property (@(A or B or OP) (OP==OP_MUL));
  cover property (@(A or B or OP) (OP==OP_DIV));

  // Edge cases
  cover property (@(A or B or OP) (OP==OP_ADD && ({1'b0,A}+{1'b0,B})[4]));          // add overflow
  cover property (@(A or B or OP) (OP==OP_SUB && (A < B)));                          // sub underflow
  cover property (@(A or B or OP) (OP==OP_MUL && (((A*B) >> 4) != 0)));              // mul overflow
  cover property (@(A or B or OP) (OP==OP_DIV && (B!=0) && ((A % B) != 0)));         // div remainder
  cover property (@(A or B or OP) (OP==OP_DIV && (B==0)));                           // div by zero

endmodule

// Bind into DUT
bind calculator calculator_sva #(.NUM_OPERATIONS(NUM_OPERATIONS)) calc_sva_i (
  .A(A), .B(B), .OP(OP), .RESULT(RESULT)
);