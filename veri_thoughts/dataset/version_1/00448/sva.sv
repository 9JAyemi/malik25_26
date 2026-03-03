// SVA for four_input_nand and nand4bb
package four_input_nand_sva_pkg;

  // Leaf-cell checker
  module nand4bb_sva (
    input logic A_N, B_N, C, D, Y, VPWR, VGND
  );
    wire pwr_good = (VPWR===1'b1 && VGND===1'b0);

    // Functional equivalence and X-prop sanity under good power
    assert property (@(A_N or B_N or C or D or VPWR or VGND)
      pwr_good |-> (Y === ~(A_N & B_N & C & D)));

    assert property (@(A_N or B_N or C or D or VPWR or VGND)
      pwr_good && !$isunknown({A_N,B_N,C,D}) |-> !$isunknown(Y));

    // Simple output-state coverage
    cover property (@(A_N or B_N or C or D or VPWR or VGND) pwr_good && (Y==1'b1));
    cover property (@(A_N or B_N or C or D or VPWR or VGND) pwr_good && (Y==1'b0));
  endmodule

  // Top-level checker (binds to internal temps)
  module four_input_nand_sva (
    input logic A_N, B_N, C, D, Y, VPWR, VGND,
    input logic temp1, temp2, temp3
  );
    wire pwr_good = (VPWR===1'b1 && VGND===1'b0);

    // Full chain correctness and simplified function (Y == A_N & B_N & C & D)
    assert property (@(A_N or B_N or C or D or VPWR or VGND or temp1 or temp2 or temp3)
      pwr_good |->
        (temp1 === ~(A_N & B_N & C & D)) &&
        (temp2 === ~temp1) &&
        (temp3 === ~temp2) &&
        (Y     === ~temp3) &&
        (Y     === (A_N & B_N & C & D)));

    // Known-in -> known-out
    assert property (@(A_N or B_N or C or D or VPWR or VGND)
      pwr_good && !$isunknown({A_N,B_N,C,D}) |-> !$isunknown(Y));

    // Input toggle coverage
    cover property (@(A_N) pwr_good && $rose(A_N));
    cover property (@(A_N) pwr_good && $fell(A_N));
    cover property (@(B_N) pwr_good && $rose(B_N));
    cover property (@(B_N) pwr_good && $fell(B_N));
    cover property (@(C)   pwr_good && $rose(C));
    cover property (@(C)   pwr_good && $fell(C));
    cover property (@(D)   pwr_good && $rose(D));
    cover property (@(D)   pwr_good && $fell(D));

    // Full 16-combo input coverage (concise)
    covergroup cg_inputs @(A_N or B_N or C or D);
      option.per_instance = 1;
      A: coverpoint A_N iff (pwr_good) { bins b0 = {0}; bins b1 = {1}; }
      B: coverpoint B_N iff (pwr_good) { bins b0 = {0}; bins b1 = {1}; }
      Cc: coverpoint C   iff (pwr_good) { bins b0 = {0}; bins b1 = {1}; }
      Dd: coverpoint D   iff (pwr_good) { bins b0 = {0}; bins b1 = {1}; }
      AXBXCXD: cross A, B, Cc, Dd;
    endgroup
    cg_inputs cg = new();

    // Power-good observed at least once
    cover property (@(VPWR or VGND) pwr_good);
  endmodule

endpackage

// Bind checkers
bind nand4bb       four_input_nand_sva_pkg::nand4bb_sva        u_nand4bb_sva (.*);
bind four_input_nand four_input_nand_sva_pkg::four_input_nand_sva u_four_input_nand_sva (.*);