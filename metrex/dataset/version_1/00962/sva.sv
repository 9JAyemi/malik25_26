// SVA for shift_register
bind shift_register shift_register_sva #(.WIDTH(WIDTH)) shift_register_sva_b();

module shift_register_sva #(parameter int WIDTH = 8) ();

  // Elaboration-time sanity
  initial assert (WIDTH >= 2)
    else $fatal(1, "shift_register WIDTH must be >= 2");

  // Past-valid tracker
  logic past_valid;
  always @(posedge clk) begin
    if (rst) past_valid <= 1'b0;
    else     past_valid <= 1'b1;
  end

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset behavior
  a_reset_clears: assert property (rst |-> reg_data == '0);

  // Exact next-state function (data_in overrides shift_in)
  a_next_state: assert property (past_valid |->
    reg_data == { $past(reg_data)[WIDTH-2:0],
                  ($past(data_in) ? 1'b1 : $past(shift_in)) });

  // Bitwise shift relation
  genvar i;
  generate
    for (i = 1; i < WIDTH; i++) begin : G
      a_bit_shift: assert property (past_valid |-> reg_data[i] == $past(reg_data[i-1]));
    end
  endgenerate

  // LSB insertion cases
  a_ins_overrides: assert property (past_valid && $past(data_in) |-> reg_data[0] == 1'b1);
  a_ins_shiftin:   assert property (past_valid && !$past(data_in) |-> reg_data[0] == $past(shift_in));

  // data_out must always mirror reg_data[0] and be 0/1
  always_comb assert (data_out === reg_data[0]);
  a_no_x_dataout: assert property (!$isunknown(data_out));
  a_no_x_state:   assert property (past_valid |-> !$isunknown(reg_data));

  // Minimal functional coverage
  c_reset_release:   cover property (rst ##1 !rst);
  c_capture_shiftin: cover property (past_valid && !$past(data_in) && $past(shift_in));
  c_override_1:      cover property (past_valid && $past(data_in) && !$past(shift_in));
  c_data_out_0:      cover property (data_out == 1'b0);
  c_data_out_1:      cover property (data_out == 1'b1);

endmodule