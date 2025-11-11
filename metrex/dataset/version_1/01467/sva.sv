// SVA checker for calculator. Bind this to the DUT.
// Uses event-based sampling and ##0 to avoid delta-cycle races.

module calculator_sva (
  input logic [7:0] A,
  input logic [7:0] B,
  input logic [1:0] op,
  input logic [7:0] result
);

  function automatic bit known8 (logic [7:0] v); return !$isunknown(v); endfunction
  function automatic bit known2 (logic [1:0] v); return !$isunknown(v); endfunction

  // Functional correctness
  property p_add;  @(A or B or op)
    known8(A) && known8(B) && known2(op) && (op==2'b00)
      |-> ##0 (result == (A + B));  // 8-bit wrap
  endproperty
  assert property (p_add);

  property p_sub;  @(A or B or op)
    known8(A) && known8(B) && known2(op) && (op==2'b01)
      |-> ##0 (result == (A - B));  // 8-bit wrap
  endproperty
  assert property (p_sub);

  property p_mul;  @(A or B or op)
    known8(A) && known8(B) && known2(op) && (op==2'b10)
      |-> ##0 (result == (A * B)[7:0]);  // truncate low 8 bits
  endproperty
  assert property (p_mul);

  property p_div;  @(A or B or op)
    known8(A) && known8(B) && known2(op) && (op==2'b11) && (B!=8'd0)
      |-> ##0 (result == (A / B));  // truncating integer division
  endproperty
  assert property (p_div);

  // Definedness (X/Z) checks
  property p_no_x_known_ops;  @(A or B or op)
    known8(A) && known8(B) && known2(op) && (op inside {2'b00,2'b01,2'b10})
      |-> ##0 ! $isunknown(result);
  endproperty
  assert property (p_no_x_known_ops);

  property p_no_x_div_when_b_nonzero;  @(A or B or op)
    known8(A) && known8(B) && known2(op) && (op==2'b11) && (B!=8'd0)
      |-> ##0 ! $isunknown(result);
  endproperty
  assert property (p_no_x_div_when_b_nonzero);

  property p_div_by_zero_yields_x;  @(A or B or op)
    known8(A) && known8(B) && known2(op) && (op==2'b11) && (B==8'd0)
      |-> ##0 $isunknown(result);
  endproperty
  assert property (p_div_by_zero_yields_x);

  // Lightweight functional covers
  cover property (@(A or B or op) known2(op) && op==2'b00 ##0 1);  // add seen
  cover property (@(A or B or op) known2(op) && op==2'b01 ##0 1);  // sub seen
  cover property (@(A or B or op) known2(op) && op==2'b10 ##0 1);  // mul seen
  cover property (@(A or B or op) known2(op) && op==2'b11 ##0 1);  // div seen

  // Corner-case covers
  cover property (@(A or B or op)
    known8(A)&&known8(B)&&op==2'b00 && ((A + B) < A));               // add overflow wrap
  cover property (@(A or B or op)
    known8(A)&&known8(B)&&op==2'b01 && (A < B));                      // sub underflow wrap
  cover property (@(A or B or op)
    known8(A)&&known8(B)&&op==2'b10 && ((A*B)[15:8] != 8'h00));       // mul overflow (high bits nonzero)
  cover property (@(A or B or op)
    known8(A)&&known8(B)&&op==2'b11 && (B!=0) && ((A % B) != 0));     // div truncation (remainder nonzero)
  cover property (@(A or B or op)
    known8(A)&&known8(B)&&op==2'b11 && (B==0));                       // divide-by-zero hit

endmodule

// Bind into DUT (in testbench or a bind file)
// bind calculator calculator_sva i_calculator_sva (.A(A), .B(B), .op(op), .result(result));