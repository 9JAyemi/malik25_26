// SVA for karnaugh_map
module karnaugh_map_sva (
  input logic A, B, C, D,
  input logic F
);

  // Any input edge as the sampling event, use ##0 to avoid race with combinational update
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge C or negedge C or
    posedge D or negedge D
  ); endclocking

  // Expected function: F = (~A & ~B & D) | (B & C & ~D)
  logic exp;
  assign exp = (~A & ~B & D) | (B & C & ~D);

  // Functional equivalence (core check)
  a_func: assert property (1'b1 |-> ##0 (F === exp))
    else $error("karnaugh_map mismatch: F=%0b exp=%0b for A B C D=%0b%0b%0b%0b", F, exp, A, B, C, D);

  // Knownness: if inputs are known, output must be known
  a_known: assert property ((!$isunknown({A,B,C,D})) |-> ##0 (!$isunknown(F)))
    else $error("karnaugh_map F unknown with known inputs A B C D=%0b%0b%0b%0b", A, B, C, D);

  // Basic toggle coverage on output
  c_F1: cover property (##0 F);
  c_F0: cover property (##0 !F);

  // Full input-space coverage (all 16 input combinations observed at least once)
  genvar i;
  generate
    for (i=0; i<16; i++) begin : cv_all_vecs
      c_vec: cover property (##0 {A,B,C,D} == i[3:0]);
    end
  endgenerate

  // Explicit coverage for on-set and off-set regions
  c_onset:  cover property (##0 ({A,B,C,D} inside {4'b0001,4'b0011,4'b0110,4'b1110}) && F);
  c_offset: cover property (##0 (!({A,B,C,D} inside {4'b0001,4'b0011,4'b0110,4'b1110}) && !F));

endmodule

// Bind into DUT
bind karnaugh_map karnaugh_map_sva sva_kmap (.*);