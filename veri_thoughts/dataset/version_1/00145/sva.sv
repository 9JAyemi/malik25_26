// SVA bind for sky130_fd_sc_hdll__a222oi
module sky130_fd_sc_hdll__a222oi_sva (
  input  logic A1, A2, B1, B2, C1, C2,
  input  logic nand0_out, nand1_out, nand2_out,
  input  logic and0_out_Y,
  input  logic Y
);

  default clocking cb @ (A1 or A2 or B1 or B2 or C1 or C2); endclocking

  function automatic bit all_known6 (input logic [5:0] v);
    return !$isunknown(v);
  endfunction

  // Functional equivalence when inputs are known
  assert property ( all_known6({A1,A2,B1,B2,C1,C2})
                    |-> (! $isunknown(Y) &&
                         (Y == ((~(A1 & A2)) & (~(B1 & B2)) & (~(C1 & C2))))) )
    else $error("Y functional mismatch");

  // Internal gate checks (no X when inputs known and correct values)
  assert property ( !$isunknown({A1,A2})
                    |-> (! $isunknown(nand0_out) && (nand0_out == ~(A1 & A2))) )
    else $error("nand0_out mismatch");

  assert property ( !$isunknown({B1,B2})
                    |-> (! $isunknown(nand1_out) && (nand1_out == ~(B1 & B2))) )
    else $error("nand1_out mismatch");

  assert property ( !$isunknown({C1,C2})
                    |-> (! $isunknown(nand2_out) && (nand2_out == ~(C1 & C2))) )
    else $error("nand2_out mismatch");

  assert property ( !$isunknown({nand0_out,nand1_out,nand2_out})
                    |-> (! $isunknown(and0_out_Y) &&
                         (and0_out_Y == (nand0_out & nand1_out & nand2_out))) )
    else $error("and0_out_Y mismatch");

  assert property ( !$isunknown(and0_out_Y)
                    |-> (! $isunknown(Y) && (Y == and0_out_Y)) )
    else $error("buf/Y mismatch");

  // Sanity: any pair == 11 implies Y == 0 (when inputs known)
  assert property ( all_known6({A1,A2,B1,B2,C1,C2}) &&
                    ((A1 & A2) || (B1 & B2) || (C1 & C2))
                    |-> (Y == 1'b0) )
    else $error("Y should be 0 when any pair is 11");

  // Coverage
  cover property ( all_known6({A1,A2,B1,B2,C1,C2}) && (Y == 1) );
  cover property ( all_known6({A1,A2,B1,B2,C1,C2}) && (Y == 0) );

  // Each single-pair-11 case observed
  cover property ( all_known6({A1,A2,B1,B2,C1,C2}) &&
                   (A1 & A2) && !(B1 & B2) && !(C1 & C2) && (Y == 0) );
  cover property ( all_known6({A1,A2,B1,B2,C1,C2}) &&
                   !(A1 & A2) && (B1 & B2) && !(C1 & C2) && (Y == 0) );
  cover property ( all_known6({A1,A2,B1,B2,C1,C2}) &&
                   !(A1 & A2) && !(B1 & B2) && (C1 & C2) && (Y == 0) );

  // Case where no pair is 11 -> Y high
  cover property ( all_known6({A1,A2,B1,B2,C1,C2}) &&
                   !(A1 & A2) && !(B1 & B2) && !(C1 & C2) && (Y == 1) );

endmodule

bind sky130_fd_sc_hdll__a222oi sky130_fd_sc_hdll__a222oi_sva sva (.*);