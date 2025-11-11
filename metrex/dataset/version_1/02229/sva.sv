// SVA for decoder_2to4_adder
// Bind into the DUT to access internal signals
bind decoder_2to4_adder decoder_2to4_adder_sva();

module decoder_2to4_adder_sva;

  // Access DUT scope: clk,in,ena,cin,out,cout,in_reg,ena_reg,cin_reg,dec_out,add_out,cout_temp

  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Decoder correctness (combinational function and one-hot)
  assert property (@(posedge clk) dec_out == (ena ? (4'b0001 << in) : 4'b0000));
  assert property (@(posedge clk) ena |-> ($onehot(dec_out) && dec_out[in]));

  // Pipeline registers capture previous-cycle inputs
  assert property (@(posedge clk) past_valid |-> (in_reg  == $past(in)  &&
                                                  ena_reg == $past(ena) &&
                                                  cin_reg == $past(cin)));

  // Adder correctness
  assert property (@(posedge clk) add_out[3:2] == 2'b00);
  assert property (@(posedge clk) {cout_temp, add_out[1:0]} == (in_reg[1:0] + cin_reg));

  // Output gating and data-path composition
  assert property (@(posedge clk) ena_reg  |-> (out == (dec_out | add_out) && cout == cout_temp));
  assert property (@(posedge clk) !ena_reg |-> (out == 4'b0000 && cout == 1'b0));

  // Sanity: outputs known; upper bits mirror decoder when enabled
  assert property (@(posedge clk) !$isunknown({out, cout}));
  assert property (@(posedge clk) ena_reg |-> (out[3:2] == dec_out[3:2]));

  // Coverage: all decode values, carry/no-carry, and mixed-cycle enable condition
  cover property (@(posedge clk) ena && dec_out == 4'b0001);
  cover property (@(posedge clk) ena && dec_out == 4'b0010);
  cover property (@(posedge clk) ena && dec_out == 4'b0100);
  cover property (@(posedge clk) ena && dec_out == 4'b1000);

  cover property (@(posedge clk) past_valid && ena_reg && (in_reg==2'd3) && cin_reg && cout_temp); // carry
  cover property (@(posedge clk) past_valid && ena_reg && !(in_reg==2'd3 && cin_reg) && !cout_temp); // no carry

  // Mixed-cycle condition where ena_reg=1 but current ena=0 (dec_out=0, only adder contributes)
  cover property (@(posedge clk) past_valid && ena_reg && !ena);

endmodule