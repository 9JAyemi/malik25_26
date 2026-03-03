// SVA for sky130_fd_sc_ls__a31o
// Bind into the DUT; supply clk/rst_n from TB.

module sky130_fd_sc_ls__a31o_sva (input logic clk, rst_n);
  // Access DUT ports/nets by name via bind
  let PWR_GOOD = (VPWR===1'b1 && VGND===1'b0 && VPB===1'b1 && VNB===1'b0);
  let IN  = {A1,A2,A3,B1};
  let F   = ((A1 & A2) | (A3 & B1));

  // Functional correctness
  ap_func:  assert property (@(posedge clk) disable iff (!rst_n || !PWR_GOOD)) X === F;

  // Internal net correctness
  ap_a12:   assert property (@(posedge clk) disable iff (!rst_n || !PWR_GOOD)) A1_AND_A2 === (A1 & A2);
  ap_a3b1:  assert property (@(posedge clk) disable iff (!rst_n || !PWR_GOOD)) A3_AND_B1 === (A3 & B1);

  // No X on X when inputs are known (under power-good)
  ap_no_x:  assert property (@(posedge clk) disable iff (!rst_n || !PWR_GOOD)) (!$isunknown(IN)) |-> (!$isunknown(X));

  // Stability: if inputs hold, output holds
  ap_stb:   assert property (@(posedge clk) disable iff (!rst_n || !PWR_GOOD)) $stable(IN) |-> $stable(X);

  // Simple implications of OR-of-ANDs
  ap_imp1:  assert property (@(posedge clk) disable iff (!rst_n || !PWR_GOOD)) (A1 & A2) |-> (X===1'b1);
  ap_imp2:  assert property (@(posedge clk) disable iff (!rst_n || !PWR_GOOD)) (A3 & B1) |-> (X===1'b1);
  ap_imp0:  assert property (@(posedge clk) disable iff (!rst_n || !PWR_GOOD)) !(A1 & A2) && !(A3 & B1) |-> (X===1'b0);

  // Power/body ties sanity when in functional mode
  ap_pwr:   assert property (@(posedge clk) disable iff (!rst_n)) PWR_GOOD |-> (VPB===VPWR && VNB===VGND);

  // Coverage: key functional cases
  cp_both0: cover  property (@(posedge clk) disable iff (!rst_n || !PWR_GOOD)) !(A1 & A2) && !(A3 & B1) && (X===1'b0);
  cp_path1: cover  property (@(posedge clk) disable iff (!rst_n || !PWR_GOOD))  (A1 & A2) && !(A3 & B1) && (X===1'b1);
  cp_path2: cover  property (@(posedge clk) disable iff (!rst_n || !PWR_GOOD)) !(A1 & A2) &&  (A3 & B1) && (X===1'b1);
  cp_both1: cover  property (@(posedge clk) disable iff (!rst_n || !PWR_GOOD))  (A1 & A2) &&  (A3 & B1) && (X===1'b1);
  cp_xtgl:  cover  property (@(posedge clk) disable iff (!rst_n || !PWR_GOOD)) (X==1'b0) ##1 (X==1'b1) ##1 (X==1'b0);

  // Truth-table coverage: all 16 input combinations under power-good
  genvar i;
  generate
    for (i=0; i<16; i++) begin : g_tt
      localparam logic [3:0] V = i[3:0];
      c_tt: cover property (@(posedge clk) disable iff (!rst_n || !PWR_GOOD)) IN === V;
    end
  endgenerate
endmodule

// Bind example (connect clk/rst_n from your TB/top)
bind sky130_fd_sc_ls__a31o sky130_fd_sc_ls__a31o_sva u_a31o_sva (.clk(clk), .rst_n(rst_n));