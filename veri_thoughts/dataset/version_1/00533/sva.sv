// SVA checker for arithmetic_op
module arithmetic_op_sva (
  input  logic [7:0] a, b,
  input  logic [1:0] ctrl,
  input  logic [7:0] result
);

  // No X/Z on interface
  assert property (@(a or b or ctrl) ##0 !$isunknown({a,b,ctrl}))
    else $error("arith_op: X/Z on inputs");
  assert property (@(a or b or ctrl or result) ##0 (!$isunknown(result)) or $isunknown({a,b,ctrl}))
    else $error("arith_op: X/Z on result with known inputs");

  // Functional correctness (allow delta to settle)
  assert property (@(a or b or ctrl) (ctrl==2'b00) |-> ##0 (result == (a + b)))
    else $error("arith_op: ADD mismatch");
  assert property (@(a or b or ctrl) (ctrl==2'b01) |-> ##0 (result == (a - b)))
    else $error("arith_op: SUB mismatch");
  assert property (@(a or b or ctrl) (ctrl==2'b10) |-> ##0 (result == (a & b)))
    else $error("arith_op: AND mismatch");
  assert property (@(a or b or ctrl) (ctrl==2'b11) |-> ##0 (result == (a | b)))
    else $error("arith_op: OR mismatch");

  // ctrl must be known (avoids unintended latch behavior on X/Z)
  assert property (@(a or b or ctrl) ##0 !$isunknown(ctrl))
    else $error("arith_op: ctrl is X/Z");

  // Basic mode coverage
  cover property (@(a or b or ctrl) ##0 (ctrl==2'b00));
  cover property (@(a or b or ctrl) ##0 (ctrl==2'b01));
  cover property (@(a or b or ctrl) ##0 (ctrl==2'b10));
  cover property (@(a or b or ctrl) ##0 (ctrl==2'b11));

  // Corner-case coverage
  cover property (@(a or b or ctrl) (ctrl==2'b00) && ##0 ((a + b) < a)); // add overflow (wrap)
  cover property (@(a or b or ctrl) (ctrl==2'b01) && ##0 ((a - b) > a)); // sub underflow (wrap)
  cover property (@(a or b or ctrl) ##0 (ctrl==2'b10 && (a==8'hFF || b==8'hFF))); // AND masking
  cover property (@(a or b or ctrl) ##0 (ctrl==2'b11 && (a==8'h00 || b==8'h00))); // OR identity
  cover property (@(a or b or ctrl) ##0 (ctrl==2'b10 && a==b)); // AND idempotent case
  cover property (@(a or b or ctrl) ##0 (ctrl==2'b11 && a==b)); // OR idempotent case

endmodule

bind arithmetic_op arithmetic_op_sva sva(.a(a), .b(b), .ctrl(ctrl), .result(result));