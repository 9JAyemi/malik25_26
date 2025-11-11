// SVA for DemoInterconnect_jtag_axi_0_0_wr_status_flags_as
module wr_status_flags_as_sva (
  input logic s_dclk_o,
  input logic in_cnt,           // \gic0.gc0.count_d1_reg[5]
  input logic out,
  input logic ram_full_fb_i,
  input logic ram_full_i
);
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge s_dclk_o) past_valid <= 1'b1;

  // Functional correctness
  assert property (@(posedge s_dclk_o) past_valid |-> out == $past(in_cnt));
  assert property (@(posedge s_dclk_o) out == ram_full_fb_i);
  assert property (@(posedge s_dclk_o) past_valid |-> ram_full_i == ram_full_fb_i);

  // Coverage: propagation and toggling
  cover property (@(posedge s_dclk_o) past_valid && $rose(in_cnt) ##1 $rose(out));
  cover property (@(posedge s_dclk_o) past_valid && $fell(in_cnt) ##1 $fell(out));
  cover property (@(posedge s_dclk_o) past_valid && out==0 ##1 out==1 ##1 out==0);
  cover property (@(posedge s_dclk_o) past_valid && in_cnt==0 ##1 in_cnt==1 ##1 in_cnt==0);
endmodule

bind DemoInterconnect_jtag_axi_0_0_wr_status_flags_as wr_status_flags_as_sva u_wr_status_flags_as_sva (
  .s_dclk_o(s_dclk_o),
  .in_cnt(\gic0.gc0.count_d1_reg[5] ),
  .out(out),
  .ram_full_fb_i(ram_full_fb_i),
  .ram_full_i(ram_full_i)
);