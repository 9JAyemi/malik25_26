// SVA for sky130_fd_sc_hd__lpflow_clkinvkapwr (Y = ~A)
module sky130_fd_sc_hd__lpflow_clkinvkapwr_sva (input logic A, Y);

  // Functional equivalence for known input (sample after delta to avoid race)
  assert property (@(A) (A === 1'b0) |-> ##0 (Y === 1'b1));
  assert property (@(A) (A === 1'b1) |-> ##0 (Y === 1'b0));

  // X/Z propagation: unknown A implies unknown Y
  assert property (@(A) $isunknown(A) |-> ##0 $isunknown(Y));

  // Edge correspondence (ignore cases where previous A was unknown)
  assert property (@(posedge A) !$past($isunknown(A)) |-> ##0 $fell(Y));
  assert property (@(negedge A) !$past($isunknown(A)) |-> ##0 $rose(Y));

  // No spurious Y toggles without an A change
  assert property (@(posedge Y or negedge Y) ##0 $changed(A));

  // Coverage
  cover  property (@(posedge A) ##0 $fell(Y));
  cover  property (@(negedge A) ##0 $rose(Y));
  cover  property (@(A) $isunknown(A) ##0 $isunknown(Y));
  cover  property (@(A or Y) (A===1'b0 && Y===1'b1));
  cover  property (@(A or Y) (A===1'b1 && Y===1'b0));

endmodule

bind sky130_fd_sc_hd__lpflow_clkinvkapwr sky130_fd_sc_hd__lpflow_clkinvkapwr_sva u_sva (.A(A), .Y(Y));