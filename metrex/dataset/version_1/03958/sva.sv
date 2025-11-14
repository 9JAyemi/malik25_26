// SVA for top_module, counter, and demux_1to256
// Bind these into the DUT. Focused, high-signal-coverage checks and concise covers.

////////////////////////////////////////////////////////////
// Counter assertions
module counter_sva(input clk, input reset, input [3:0] q);
  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  a_cnt_no_x:    assert property (1'b1 |-> !$isunknown(q));
  a_cnt_in_range:assert property (!reset |-> (q inside {[4'd0:4'd15]}));

  // Reset drives 0 at clock edge when asserted
  a_cnt_rst0:    assert property (reset |-> q == 4'd0);

  // Mod-16 up-counter behavior across cycles when not in reset
  a_cnt_step:    assert property ((!reset && !$past(reset)) |-> (q == (($past(q)==4'd15) ? 4'd0 : $past(q)+4'd1)));

  // Coverage: visit all values and see wrap
  genvar i;
  generate for (i=0;i<16;i++) begin : C_CNT_VAL
    c_cnt_val: cover property (!reset && q==i[3:0]);
  end endgenerate
  c_cnt_wrap: cover property (!reset && !$past(reset) && $past(q)==4'd15 && q==4'd0);
endmodule

bind counter counter_sva counter_sva_i(.*);

////////////////////////////////////////////////////////////
// demux assertions (combinational)
// Uses immediate assertions for combinational equivalence
module demux_sva(input [31:0] in, input [3:0] sel, input [31:0] out);
  function automatic [31:0] demux_ref(input [31:0] tin, input [3:0] s);
    case (s)
      4'b0000: demux_ref = tin;
      4'b0001: demux_ref = {tin[7:0], 24'b0};
      4'b0010: demux_ref = {tin[15:0], 16'b0};
      4'b0011: demux_ref = {tin[23:0], 8'b0};
      4'b0100: demux_ref = {tin[31:24], 8'b0};
      4'b0101: demux_ref = {tin[31:20], 12'b0};
      4'b0110: demux_ref = {tin[31:16], 16'b0};
      4'b0111: demux_ref = {tin[31:12], 20'b0};
      4'b1000: demux_ref = {tin[31:8], 24'b0};
      4'b1001: demux_ref = {tin[31:4], 28'b0};
      4'b1010: demux_ref = tin;
      4'b1011: demux_ref = 32'b0;
      4'b1100: demux_ref = {tin[7:0], 24'b0};
      4'b1101: demux_ref = {tin[15:0], 16'b0};
      4'b1110: demux_ref = {tin[23:0], 8'b0};
      4'b1111: demux_ref = tin;
      default: demux_ref = 'x;
    endcase
  endfunction

  // No X on select
  always @* begin
    assert (!$isunknown(sel)) else $error("demux sel is X/Z");
    // Equivalence to reference function (X-sensitive)
    assert (out === demux_ref(in, sel)) else $error("demux out mismatch");
  end

  // Lightweight functional coverage of each select
  genvar j;
  generate for (j=0;j<16;j++) begin : C_DEMUX_SEL
    always @* cover (sel==j[3:0]);
  end endgenerate
endmodule

bind demux_1to256 demux_sva demux_sva_i(.*);

////////////////////////////////////////////////////////////
// top assertions
module top_sva(
  input clk, input reset,
  input [31:0] out,
  input [3:0]  counter_out_reg,
  input [3:0]  counter_out_next,
  input [31:0] selected_out
);
  default clocking cb @(posedge clk); endclocking

  // Basic sanities
  a_top_no_x_ctr: assert property (1'b1 |-> !$isunknown(counter_out_reg));
  a_top_ctr_range:assert property (!reset |-> (counter_out_reg inside {[4'd0:4'd15]}));
  a_top_no_x_out: assert property (1'b1 |-> !$isunknown(out));

  // Pipeline/registering behavior of counter_out_reg
  a_top_ctr_rst:  assert property (reset |-> counter_out_reg == 4'd0);
  a_top_ctr_follow: assert property ((!reset && !$past(reset)) |-> counter_out_reg == $past(counter_out_next));

  // Combinational relation for out (including zero-extension to 32b)
  function automatic [31:0] top_ref(input [31:0] s);
    top_ref = {16'b0, (s[15:8] & {8{s[7]}}), s[7:0]};
  endfunction
  a_top_out_eq: assert property (out === top_ref(selected_out));

  // Useful decomposed checks
  a_top_hi_zero: assert property (out[31:16] == 16'b0);
  a_top_lo_passthru: assert property (out[7:0] == selected_out[7:0]);
  a_top_mid_mask0: assert property (selected_out[7]==1'b0 |-> out[15:8]==8'b0);
  a_top_mid_mask1: assert property (selected_out[7]==1'b1 |-> out[15:8]==selected_out[15:8]);

  // Coverage: exercise all demux selects via registered select
  genvar k;
  generate for (k=0;k<16;k++) begin : C_TOP_SEL
    c_top_sel: cover property (!reset && counter_out_reg==k[3:0]);
  end endgenerate

  // Coverage: see both gating modes of selected_out[7]
  c_gate0: cover property (selected_out[7]==1'b0);
  c_gate1: cover property (selected_out[7]==1'b1);

  // Coverage: observe at least one clean reset pulse and recovery
  c_rst_pulse: cover property ($rose(reset));
  c_rst_release: cover property ($fell(reset));
endmodule

bind top_module top_sva top_sva_i(
  .clk(clk), .reset(reset),
  .out(out),
  .counter_out_reg(counter_out_reg),
  .counter_out_next(counter_out_next),
  .selected_out(selected_out)
);