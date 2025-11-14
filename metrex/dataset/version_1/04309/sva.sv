// SVA for top_module (concise, high-signal/functional coverage)
module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [15:0] count,
  input  logic [15:0] binary_out,
  input  logic [3:0]  bcd_out,
  input  logic [3:1]  ena_out,
  input  logic [3:1]  ena,
  input  logic [3:1]  ena_reg,
  input  logic [15:0] q
);

  default clocking cb @(posedge clk); endclocking

  // Helpers
  function automatic logic [3:0] bcd_expect (input logic [15:0] b);
    if (b <= 16'd9)       bcd_expect = b[3:0];
    else if (b <= 16'd18) bcd_expect = (b-16'd9 )[3:0];   // 10..18 -> 1..9
    else if (b <= 16'd27) bcd_expect = (b-16'd18)[3:0];   // 19..27 -> 1..9
    else if (b <= 16'd35) bcd_expect = (b-16'd27)[3:0];   // 28..35 -> 1..8
    else                  bcd_expect = 4'h0;
  endfunction

  // Reset behavior
  a_reset_vals:    assert property (reset |-> (count==16'h0 && ena_reg==3'b000));

  // Counter behavior
  a_count_inc:     assert property (!reset && !$past(reset) |-> count == $past(count)+16'h1);
  a_count_wrap:    assert property (!reset && $past(!reset) && $past(count)==16'hFFFF |-> count==16'h0000);

  // Static/comb links
  a_bin_link:      assert property (binary_out == count);
  a_ena_const:     assert property (ena_out == 3'b111);
  a_prienc:        assert property (ena == ~ena_out);
  a_ena_reg_samp:  assert property (!reset |-> ena_reg == $past(ena_out));

  // Output formatting
  a_q_layout:      assert property (q[11:0]==12'h000 && q[15:12]==bcd_out);

  // BCD mapping correctness (for all values)
  a_bcd_map:       assert property (bcd_out == bcd_expect(binary_out));

  // Basic X-checks on key outputs
  a_no_x:          assert property (!$isunknown({ena, q, bcd_out}));

  // Coverage
  c_reset_cycle:   cover  property (reset ##1 !reset);
  c_wrap:          cover  property (!reset && $past(!reset) && $past(count)==16'hFFFF && count==16'h0000);

  // Exercise key BCD boundary points via the free-running counter
  c_bcd_0:         cover  property (!reset && binary_out==16'd0);
  c_bcd_9:         cover  property (!reset && binary_out==16'd9);
  c_bcd_10:        cover  property (!reset && binary_out==16'd10);
  c_bcd_18:        cover  property (!reset && binary_out==16'd18);
  c_bcd_19:        cover  property (!reset && binary_out==16'd19);
  c_bcd_27:        cover  property (!reset && binary_out==16'd27);
  c_bcd_28:        cover  property (!reset && binary_out==16'd28);
  c_bcd_35:        cover  property (!reset && binary_out==16'd35);
  c_bcd_36_def:    cover  property (!reset && binary_out==16'd36); // default branch
  c_enc_zero:      cover  property (!reset && ena==3'b000);

endmodule

bind top_module top_module_sva u_top_sva (
  .clk       (clk),
  .reset     (reset),
  .count     (count),
  .binary_out(binary_out),
  .bcd_out   (bcd_out),
  .ena_out   (ena_out),
  .ena       (ena),
  .ena_reg   (ena_reg),
  .q         (q)
);