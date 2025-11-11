// SVA for AND4_W9: structural correctness, functional equivalence, and compact coverage
// Bind into the DUT to observe internals without modifying RTL.

module AND4_W9_sva;
  // Bind scope sees: A, Y, n1, n2, n3
  default clocking cb @(
      posedge A[0] or negedge A[0] or
      posedge A[1] or negedge A[1] or
      posedge A[2] or negedge A[2] or
      posedge A[3] or negedge A[3]
  ); endclocking

  // Structural relations
  assert property (n1 === ~(A[0] & A[1]));
  assert property (n2 === ~(A[2] & A[3]));
  assert property (n3 === ~(n1   & n2));
  assert property (Y  === ~n3);

  // Collapsed functional relation (end-to-end)
  assert property (Y === ((~(A[0] & A[1])) & (~(A[2] & A[3]))));

  // 4-state sanity: if inputs are known, all internal nets and Y are known
  assert property (!$isunknown(A) |-> (!$isunknown(n1) && !$isunknown(n2) && !$isunknown(n3) && !$isunknown(Y)));

  // Compact functional coverage
  // - Hit every input combination (0..15)
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : g_cov
      localparam logic [3:0] VAL = i[3:0];
      cover property (A == VAL);
    end
  endgenerate
  // - Observe both output polarities and key corners
  cover property (Y == 1'b1);
  cover property (Y == 1'b0);
  cover property ((A == 4'h0) && (Y == 1'b1));
  cover property ((A == 4'hF) && (Y == 1'b0));
endmodule

bind AND4_W9 AND4_W9_sva AND4_W9_sva_inst();