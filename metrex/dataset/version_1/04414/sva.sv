// SVA for nor4. Bind to DUT; concise, functionally complete.

`ifndef SYNTHESIS
module nor4_sva (input logic A, B, C, D, Y);

  // Functional correctness when inputs are known
  assert property (@(A or B or C or D or Y)
                   !$isunknown({A,B,C,D}) |-> (Y == ~(|{A,B,C,D})))
    else $error("nor4: Y != ~(A|B|C|D) with known inputs");

  // Safe partial-knowledge checks (work even if some inputs are X/Z)
  assert property (@(A or B or C or D or Y) (|{A,B,C,D}) === 1 |-> (Y == 0))
    else $error("nor4: Y must be 0 when any input is 1");
  assert property (@(A or B or C or D or Y) (|{A,B,C,D}) === 0 |-> (Y == 1))
    else $error("nor4: Y must be 1 when all inputs are 0");

  // Functional coverage: all 16 input combinations with expected Y
  cover property (@(A or B or C or D or Y) ({A,B,C,D} == 4'b0000) && (Y == 1));
  cover property (@(A or B or C or D or Y) ({A,B,C,D} == 4'b0001) && (Y == 0));
  cover property (@(A or B or C or D or Y) ({A,B,C,D} == 4'b0010) && (Y == 0));
  cover property (@(A or B or C or D or Y) ({A,B,C,D} == 4'b0011) && (Y == 0));
  cover property (@(A or B or C or D or Y) ({A,B,C,D} == 4'b0100) && (Y == 0));
  cover property (@(A or B or C or D or Y) ({A,B,C,D} == 4'b0101) && (Y == 0));
  cover property (@(A or B or C or D or Y) ({A,B,C,D} == 4'b0110) && (Y == 0));
  cover property (@(A or B or C or D or Y) ({A,B,C,D} == 4'b0111) && (Y == 0));
  cover property (@(A or B or C or D or Y) ({A,B,C,D} == 4'b1000) && (Y == 0));
  cover property (@(A or B or C or D or Y) ({A,B,C,D} == 4'b1001) && (Y == 0));
  cover property (@(A or B or C or D or Y) ({A,B,C,D} == 4'b1010) && (Y == 0));
  cover property (@(A or B or C or D or Y) ({A,B,C,D} == 4'b1011) && (Y == 0));
  cover property (@(A or B or C or D or Y) ({A,B,C,D} == 4'b1100) && (Y == 0));
  cover property (@(A or B or C or D or Y) ({A,B,C,D} == 4'b1101) && (Y == 0));
  cover property (@(A or B or C or D or Y) ({A,B,C,D} == 4'b1110) && (Y == 0));
  cover property (@(A or B or C or D or Y) ({A,B,C,D} == 4'b1111) && (Y == 0));

endmodule

bind nor4 nor4_sva i_nor4_sva (.*);
`endif