// SVA for shift_register
module shift_register_sva (
  input logic        clk,
  input logic [3:0]  data_in,
  input logic        shift_right,
  input logic        load,
  input logic [3:0]  data_out,
  input logic [3:0]  reg_q  // connect to DUT's internal "register"
);

  default clocking cb @(posedge clk); endclocking

  // Guard $past at time 0
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;
  default disable iff (!past_valid);

  function automatic logic [3:0] rol1 (input logic [3:0] v);
    return {v[2:0], v[3]};
  endfunction

  // Basic sanity
  a_no_x_ctrl:         assert property (!$isunknown({load, shift_right}));
  a_no_x_data_on_load: assert property (load |-> !$isunknown(data_in));

  // Output mirrors internal register (combinational hookup)
  a_mirror:            assert property (data_out == reg_q);

  // Synchronous behavior
  // Load has priority
  a_load:              assert property (load |=> data_out == $past(data_in));

  // When not loading and shift_right=1, design rotates LEFT by 1 bit
  a_shift_rotate_l:    assert property ((!load && shift_right) |=> data_out == rol1($past(data_out)));

  // When neither loading nor shifting, hold value
  a_hold:              assert property ((!load && !shift_right) |=> data_out == $past(data_out));

  // Bit-level map for the rotate-left case (extra clarity)
  a_shift_bitmap:      assert property ((!load && shift_right) |=> 
                                        (data_out[0] == $past(data_out[3]) &&
                                         data_out[3:1] == $past(data_out[2:0])));

  // Functional coverage
  c_load:              cover property (load);
  c_shift:             cover property (!load && shift_right);
  c_hold:              cover property (!load && !shift_right);
  c_both:              cover property (load && shift_right); // load priority exercised
  // 4 consecutive rotates return to original value
  c_full_rotate:       cover property ((!load && shift_right)[*4] ##1 (data_out == $past(data_out,4)));

endmodule

// Bind into DUT
bind shift_register shift_register_sva sva_i (
  .clk       (clk),
  .data_in   (data_in),
  .shift_right(shift_right),
  .load      (load),
  .data_out  (data_out),
  .reg_q     (register)
)