// SVA for adder_2bit
// Concise functional checks + key coverage.
// Assumes 2-bit arithmetic with wraparound; S[0]=0 => add, S[0]=1 => subtract.

module adder_2bit_sva (
  input logic [1:0] A,
  input logic [1:0] B,
  input logic [1:0] S,
  input logic [1:0] O
);

  function automatic logic [1:0] add2 (input logic [1:0] x, y);
    add2 = x + y; // truncates to 2 bits
  endfunction

  function automatic logic [1:0] sub2 (input logic [1:0] x, y);
    sub2 = x - y; // truncates to 2 bits
  endfunction

  function automatic bit add_carry (input logic [1:0] x, y);
    add_carry = ({1'b0,x} + {1'b0,y})[2];
  endfunction

  function automatic bit sub_borrow (input logic [1:0] x, y);
    sub_borrow = ({1'b0,x} - {1'b0,y})[2]; // 1 means borrow (underflow)
  endfunction

  // No X/Z on O whenever inputs are known
  assert property (@(A or B or S or O) !$isunknown({A,B,S}) |-> !$isunknown(O))
    else $error("O has X/Z with known inputs");

  // Functional correctness: add when S[0]==0
  assert property (@(A or B or S or O)
                   (!$isunknown({A,B,S[0]})) && (S[0]==1'b0) |-> O == add2(A,B))
    else $error("Add path incorrect: O != A+B (mod 4)");

  // Functional correctness: subtract when S[0]==1
  assert property (@(A or B or S or O)
                   (!$isunknown({A,B,S[0]})) && (S[0]==1'b1) |-> O == sub2(A,B))
    else $error("Sub path incorrect: O != A-B (mod 4)");

  // S[1] should not affect output (detects unintended sensitivity to upper S bit)
  assert property (@(posedge S[1] or negedge S[1])
                   $stable(A) && $stable(B) && $stable(S[0]) |-> $stable(O))
    else $error("O depends on S[1], which should be unused");

  // Coverage: exercise add path
  cover property (@(A or B or S) (S[0]==0) && !$isunknown({A,B}) && O==add2(A,B));

  // Coverage: exercise sub path
  cover property (@(A or B or S) (S[0]==1) && !$isunknown({A,B}) && O==sub2(A,B));

  // Coverage: add overflow (wrap)
  cover property (@(A or B) add_carry(A,B));

  // Coverage: sub underflow (borrow)
  cover property (@(A or B) sub_borrow(A,B));

  // Coverage: corner outputs
  cover property (@(A or B or S) O==2'b00);
  cover property (@(A or B or S) O==2'b11);

endmodule

// Bind into DUT
bind adder_2bit adder_2bit_sva sva_adder_2bit (.*);