// SVA for arithmetic. Combinational checks use event-based sampling with ##0 to wait for settle.
module arithmetic_sva (
  input  logic [7:0]  a,
  input  logic [7:0]  b,
  input  logic [1:0]  op,
  input  logic [15:0] result
);
  // zero-extended 16-bit operands for expected arithmetic
  let A16 = {8'h00, a};
  let B16 = {8'h00, b};

  // Correctness per opcode
  ap_add: assert property (@(a or b or op) (op==2'b00) |-> ##0 (result == (A16 + B16)));
  ap_sub: assert property (@(a or b or op) (op==2'b01) |-> ##0 (result == (A16 - B16)));
  ap_mul: assert property (@(a or b or op) (op==2'b10) |-> ##0 (result == (a * b)));           // 8x8 -> 16
  ap_div_nozero: assert property (@(a or b or op) (op==2'b11) |-> (b != 0));                    // forbid /0
  ap_div: assert property (@(a or b or op) (op==2'b11 && b!=0) |-> ##0 (result == {8'h00,(a/b)}));

  // Knownness: with known inputs and legal divide, result must be known
  ap_known: assert property (@(a or b or op or result)
                             (!$isunknown({a,b,op}) && !(op==2'b11 && b==0)) |-> ##0 !$isunknown(result));

  // Functional coverage
  cv_add: cover property (@(a or b or op) op==2'b00);
  cv_sub: cover property (@(a or b or op) op==2'b01);
  cv_mul: cover property (@(a or b or op) op==2'b10);
  cv_div: cover property (@(a or b or op) op==2'b11 && b!=0);

  // Corner-case coverage
  cv_add_overflow:   cover property (@(a or b or op) op==2'b00 && ({1'b0,a}+{1'b0,b})[8]);
  cv_sub_underflow:  cover property (@(a or b or op) op==2'b01 && (a < b));
  cv_mul_max:        cover property (@(a or b or op) op==2'b10 && a==8'hFF && b==8'hFF);
  cv_div_exact:      cover property (@(a or b or op) op==2'b11 && b!=0 && (a % b == 0));
  cv_div_remainder:  cover property (@(a or b or op) op==2'b11 && b!=0 && (a % b != 0));
  cv_div_by_zero_try:cover property (@(a or b or op) op==2'b11 && b==0); // track illegal stimulus
endmodule

// Bind into DUT
bind arithmetic arithmetic_sva u_arithmetic_sva (.a(a), .b(b), .op(op), .result(result));