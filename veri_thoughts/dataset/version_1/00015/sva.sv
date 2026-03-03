// SVA for MUX_2_TO_1
// Bindable checker, concise but with high-quality checks and coverage
`ifndef MUX_2_TO_1_SVA
`define MUX_2_TO_1_SVA

module MUX_2_TO_1_sva (input logic A, B, S, Z);
  timeunit 1ns; timeprecision 1ps;

  // Functional correctness after delta
  assert property (@(A or B or S or Z) 1'b1 |-> ##0 (Z === ((S==1'b0) ? A : B)))
    else $error("MUX mismatch: Z=%0b S=%0b A=%0b B=%0b", Z,S,A,B);

  // Non-selected input must not affect Z
  assert property (@(A or B or S)
                   (S===1'b0 && $changed(B) && $stable(A) && $stable(S)) |-> ##0 $stable(Z))
    else $error("Z changed due to B while S==0");
  assert property (@(A or B or S)
                   (S===1'b1 && $changed(A) && $stable(B) && $stable(S)) |-> ##0 $stable(Z))
    else $error("Z changed due to A while S==1");

  // Selected input must propagate to Z
  assert property (@(A or B or S)
                   (S===1'b0 && $changed(A) && $stable(B) && $stable(S)) |-> ##0 (Z === A))
    else $error("A did not propagate when S==0");
  assert property (@(A or B or S)
                   (S===1'b1 && $changed(B) && $stable(A) && $stable(S)) |-> ##0 (Z === B))
    else $error("B did not propagate when S==1");

  // Z reacts correctly to S toggle
  assert property (@(S or A or B)
                   ($stable(A) && $stable(B) && (A!==B) && $changed(S)) |-> ##0 $changed(Z))
    else $error("Z did not change on S toggle when A!=B");
  assert property (@(S or A or B)
                   ($stable(A) && $stable(B) && (A===B) && $changed(S)) |-> ##0 $stable(Z))
    else $error("Z changed on S toggle when A==B");

  // Optional knownness checks
  assert property (@(S) (S===1'b0 || S===1'b1))
    else $error("S is X/Z");
  assert property (@(A or B or S)
                   (S===1'b0 && !$isunknown(A)) |-> ##0 !$isunknown(Z))
    else $error("Z unknown with S==0 and A known");
  assert property (@(A or B or S)
                   (S===1'b1 && !$isunknown(B)) |-> ##0 !$isunknown(Z))
    else $error("Z unknown with S==1 and B known");

  // Coverage
  cover property (@(A or B or S or Z) (S===1'b0 && Z===A));
  cover property (@(A or B or S or Z) (S===1'b1 && Z===B));
  cover property (@(A or B or S) (S===1'b0 && $changed(A) && $stable(B) && $stable(S)) |-> ##0 $changed(Z));
  cover property (@(A or B or S) (S===1'b1 && $changed(B) && $stable(A) && $stable(S)) |-> ##0 $changed(Z));
  cover property (@(S) $changed(S));

endmodule

bind MUX_2_TO_1 MUX_2_TO_1_sva (.A(A), .B(B), .S(S), .Z(Z));

`endif