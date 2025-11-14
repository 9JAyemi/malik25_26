// SVA for karnaugh_map: F must equal B^C^D; independent of A; full input coverage; no X/Z.
module karnaugh_map_sva(input logic A,B,C,D, input logic F);

  // Trigger checks on any input edge; use ##0 to avoid preponed sampling
  default clocking cb @(posedge A or negedge A or
                        posedge B or negedge B or
                        posedge C or negedge C or
                        posedge D or negedge D); endclocking

  // No unknowns on inputs or output
  assert property (##0 !$isunknown({A,B,C,D,F}))
    else $error("karnaugh_map: X/Z on {A,B,C,D,F}");

  // Functional equivalence (concise full truth table)
  assert property (##0 F == (B ^ C ^ D))
    else $error("karnaugh_map: F != B^C^D");

  // F must not change unless B, C, or D change (independence from A)
  assert property (##0 $stable({B,C,D}) |-> $stable(F))
    else $error("karnaugh_map: F changed while B,C,D stable");

  // Functional coverage: all 16 input combinations hit with correct F
  // Ones set for {B,C,D} = 001,010,100,111 (for both A=0 and A=1)
  cover property (##0 (A==1'b0) && ({B,C,D} inside {3'b001,3'b010,3'b100,3'b111}) && F);
  cover property (##0 (A==1'b1) && ({B,C,D} inside {3'b001,3'b010,3'b100,3'b111}) && F);

  // Zeros set for {B,C,D} = 000,011,101,110 (for both A=0 and A=1)
  cover property (##0 (A==1'b0) && ({B,C,D} inside {3'b000,3'b011,3'b101,3'b110}) && !F);
  cover property (##0 (A==1'b1) && ({B,C,D} inside {3'b000,3'b011,3'b101,3'b110}) && !F);

endmodule

// Bind into DUT
bind karnaugh_map karnaugh_map_sva sva_i(.A(A),.B(B),.C(C),.D(D),.F(F));