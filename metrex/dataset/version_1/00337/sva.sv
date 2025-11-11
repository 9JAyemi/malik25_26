Below is a concise, high-quality SVA package (bindable) that fully checks and covers the key behaviors of the module, including reset, up/down counter semantics, 1k divider FSM, pipeline relationships, and pass-through outputs.

module my_fpga_sva(
  input  logic        clk,
  input  logic        n_rst,
  input  logic        up,
  input  logic        dn,
  input  logic [31:0] cnt,
  input  logic [3:0]  cnt_1k,
  input  logic        in1,
  input  logic        in2,
  input  logic        out1,
  input  logic        out2,
  // internal signals
  input  logic [31:0] cnt_reg,
  input  logic [3:0]  cnt_1k_reg,
  input  logic [31:0] cnt_1k_divider,
  input  logic [31:0] cnt_1k_divider_reg,
  input  logic        cnt_1k_enable
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!n_rst);

  logic past_valid;
  always_ff @(posedge clk or negedge n_rst) begin
    if (!n_rst) past_valid <= 1'b0;
    else        past_valid <= 1'b1;
  end

  // Reset state holds while reset asserted (async reset observable on clk edge)
  assert property (!n_rst |-> (cnt_reg==0 && cnt_1k_reg==0 && cnt_1k_divider==0 && cnt_1k_divider_reg==0 && cnt_1k_enable==0));

  // Up/Down counter semantics
  assert property (past_valid &&  up && !dn |=> cnt_reg == $past(cnt_reg) + 32'd1);
  assert property (past_valid && !up &&  dn |=> cnt_reg == $past(cnt_reg) - 32'd1);
  assert property (past_valid && ((up && dn) || (!up && !dn)) |=> cnt_reg == $past(cnt_reg));

  // cnt is a 1-cycle pipeline of cnt_reg
  assert property (past_valid |-> cnt == $past(cnt_reg));

  // 1k divider next-state function and range
  assert property (past_valid && $past(cnt_1k_divider_reg)==32'd0 |-> cnt_1k_divider_reg==32'd100000);
  assert property (past_valid && $past(cnt_1k_divider_reg)==32'd1 |-> cnt_1k_divider_reg==32'd0);
  assert property (past_valid && ($past(cnt_1k_divider_reg) inside {[2:100000]})
                   |-> cnt_1k_divider_reg == $past(cnt_1k_divider_reg) - 32'd1);
  assert property (cnt_1k_divider_reg <= 32'd100000);
  assert property (cnt_1k_divider     <= 32'd100000);

  // 1k counter updates only on divider==0, with wrap at 0xF
  assert property (past_valid && $past(cnt_1k_divider_reg)==32'd0 && $past(cnt_1k_reg)!=4'hF
                   |-> cnt_1k_reg == $past(cnt_1k_reg) + 4'd1);
  assert property (past_valid && $past(cnt_1k_divider_reg)==32'd0 && $past(cnt_1k_reg)==4'hF
                   |-> cnt_1k_reg == 4'd0);
  assert property (past_valid && $past(cnt_1k_divider_reg)!=32'd0
                   |-> cnt_1k_reg == $past(cnt_1k_reg));

  // Pipelining of 1k signals
  assert property (past_valid |-> cnt_1k          == $past(cnt_1k_reg));
  assert property (past_valid |-> cnt_1k_divider  == $past(cnt_1k_divider_reg));

  // Enable stays asserted out of reset
  assert property (cnt_1k_enable);

  // Pass-through outputs (1-cycle latency)
  assert property (past_valid |-> out1 == $past(in1));
  assert property (past_valid |-> out2 == $past(in2));

  // Useful coverage
  cover property (past_valid &&  up && !dn ##1 !up &&  dn);              // inc then dec
  cover property (past_valid &&  up &&  dn);                              // both high (hold)
  cover property (past_valid && cnt_1k_divider_reg==32'd0 ##1 cnt_1k_divider_reg==32'd100000);
  cover property (past_valid && $past(cnt_1k_divider_reg)==32'd0 && $past(cnt_1k_reg)==4'hF ##1 cnt_1k_reg==4'd0);
  cover property (past_valid && $past(cnt_reg)==32'hFFFF_FFFF &&  up && !dn ##1 cnt_reg==32'h0000_0000); // inc wrap
  cover property (past_valid && $past(cnt_reg)==32'h0000_0000 && !up &&  dn ##1 cnt_reg==32'hFFFF_FFFF); // dec wrap
  cover property (past_valid && in1 != $past(in1) ##1 out1 == $past(in1));

endmodule

// Example bind (place in TB or a package included by TB)
bind my_fpga my_fpga_sva sva_i(
  .clk(clk),
  .n_rst(n_rst),
  .up(up),
  .dn(dn),
  .cnt(cnt),
  .cnt_1k(cnt_1k),
  .in1(in1),
  .in2(in2),
  .out1(out1),
  .out2(out2),
  .cnt_reg(cnt_reg),
  .cnt_1k_reg(cnt_1k_reg),
  .cnt_1k_divider(cnt_1k_divider),
  .cnt_1k_divider_reg(cnt_1k_divider_reg),
  .cnt_1k_enable(cnt_1k_enable)
);