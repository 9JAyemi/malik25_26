// SVA for top_module pipeline (binary_to_gray -> barrel_shifter -> final_output)
// Provide a sampling clock/reset from your TB. Bind example at bottom.

module top_module_sva #(parameter W=16) (
  input  logic                  clk,
  input  logic                  rst_n,

  // tap DUT scope signals
  input  logic [W-1:0]          data_in,
  input  logic [3:0]            shift_amount,
  input  logic                  control,
  input  logic [W-1:0]          gray_out,
  input  logic [W-1:0]          shifted_data_out,
  input  logic [W-1:0]          data_out
);
  default clocking cb @ (posedge clk); endclocking
  default disable iff (!rst_n);

  // Basic sanity
  a_inputs_known:  assert property (!$isunknown({data_in, shift_amount, control}));
  a_outputs_known: assert property ((!$isunknown({data_in, shift_amount, control})) |-> !$isunknown({gray_out, shifted_data_out, data_out}));

  // Stage correctness
  a_gray_eq:       assert property (gray_out == (data_in ^ (data_in >> 1)));
  a_shift_eq:      assert property (shifted_data_out == (control ? (gray_out >> shift_amount)
                                                                : (gray_out << shift_amount)));
  a_final_and_eq:  assert property (data_out == (gray_out & shifted_data_out));

  // Useful boundary/consistency checks
  a_shift0:        assert property ((shift_amount == 0) |-> (shifted_data_out == gray_out && data_out == gray_out));
  a_shift15_L:     assert property ((control==1'b0 && shift_amount==4'd15) |-> shifted_data_out == {gray_out[0], {W-1{1'b0}}});
  a_shift15_R:     assert property ((control==1'b1 && shift_amount==4'd15) |-> shifted_data_out == {{W-1{1'b0}}, gray_out[W-1]});

  // Minimal but meaningful coverage
  c_ctrl0:         cover property (control==1'b0);
  c_ctrl1:         cover property (control==1'b1);
  c_sh0:           cover property (shift_amount==4'd0);
  c_sh1:           cover property (shift_amount==4'd1);
  c_sh8:           cover property (shift_amount==4'd8);
  c_sh15:          cover property (shift_amount==4'd15);
  c_din_zero:      cover property (data_in=={W{1'b0}});
  c_din_ones:      cover property (data_in=={W{1'b1}});
  c_din_msb:       cover property (data_in==({1'b1,{W-1{1'b0}}}));
  c_din_lsb:       cover property (data_in==({{W-1{1'b0}},1'b1}));

  // End-to-end functional cover (AND of gray and shifted(gray)) in both directions
  c_end_ctrl0:     cover property (control==1'b0 ##0 data_out == ( (data_in ^ (data_in>>1)) & ((data_in ^ (data_in>>1)) << shift_amount) ));
  c_end_ctrl1:     cover property (control==1'b1 ##0 data_out == ( (data_in ^ (data_in>>1)) & ((data_in ^ (data_in>>1)) >> shift_amount) ));
endmodule

// Bind example (adapt clk/rst_n paths to your TB):
// bind top_module top_module_sva #(.W(16)) u_top_sva ( .clk(tb_clk), .rst_n(tb_rst_n),
//   .data_in(data_in), .shift_amount(shift_amount), .control(control),
//   .gray_out(gray_out), .shifted_data_out(shifted_data_out), .data_out(data_out) );