// SVA for D_posedge_async
module D_posedge_async_sva(input Q, input Qn, input rst_l, input D, input clk);

  default clocking cb @(posedge clk); endclocking

  // Core behavior
  a_sync_reset:  assert property (!rst_l |-> (Q == 1'b0 && Qn == 1'b1));
  a_capture:     assert property ( rst_l |-> (Q == D     && Qn == ~D));

  // Outputs complementary whenever known
  a_complement:  assert property ((!$isunknown({Q,Qn})) |-> (Qn == ~Q));

  // No X on outputs when inputs are known
  a_no_x:        assert property ((rst_l && !$isunknown(D)) |-> !$isunknown({Q,Qn}));

  // Coverage
  c_reset:       cover  property (!rst_l);
  c_release:     cover  property (!rst_l ##1 rst_l);
  c_cap0:        cover  property (rst_l && D == 1'b0);
  c_cap1:        cover  property (rst_l && D == 1'b1);
  c_toggle:      cover  property (rst_l && D == 1'b0 ##1 rst_l && D == 1'b1);

endmodule

bind D_posedge_async D_posedge_async_sva sva(.Q(Q), .Qn(Qn), .rst_l(rst_l), .D(D), .clk(clk));