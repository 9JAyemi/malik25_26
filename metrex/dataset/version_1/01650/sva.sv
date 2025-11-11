// SVA for sky130_fd_sc_hd__nor2b (Y = ~A & B_N)
module sky130_fd_sc_hd__nor2b_sva (input logic A, B_N, Y);

  // Core functional equivalence (check after delta to avoid race)
  assert property (@(A or B_N) ##0 (Y === (~A & B_N)))
    else $error("nor2b func mismatch: Y != (~A & B_N) after input change");

  // Guard against unintended Y glitches
  assert property (@(Y) ##0 (Y === (~A & B_N)))
    else $error("nor2b glitch: Y changed but != (~A & B_N)");

  // Strong zero-forcing corners
  assert property (@(A or B_N) (B_N === 1'b0) |-> ##0 (Y === 1'b0));
  assert property (@(A or B_N) (A   === 1'b1) |-> ##0 (Y === 1'b0));

  // X-propagation sanity
  assert property (@(A or B_N) (B_N === 1'b1 && $isunknown(A)) |-> ##0 $isunknown(Y));
  assert property (@(A or B_N) (A   === 1'b1 && $isunknown(B_N)) |-> ##0 (Y === 1'b0));

  // Truth-table coverage
  cover property (@(A or B_N) ##0 (A===1'b0 && B_N===1'b0 && Y===1'b0));
  cover property (@(A or B_N) ##0 (A===1'b0 && B_N===1'b1 && Y===1'b1));
  cover property (@(A or B_N) ##0 (A===1'b1 && B_N===1'b0 && Y===1'b0));
  cover property (@(A or B_N) ##0 (A===1'b1 && B_N===1'b1 && Y===1'b0));

  // Output transition coverage
  cover property (@(posedge Y) ##0 (A===1'b0 && B_N===1'b1));
  cover property (@(negedge Y) ##0 (A===1'b1 || B_N===1'b0));

endmodule

bind sky130_fd_sc_hd__nor2b sky130_fd_sc_hd__nor2b_sva sva_inst (.*);