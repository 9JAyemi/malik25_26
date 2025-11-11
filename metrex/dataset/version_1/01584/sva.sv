// SVA checkers and binds for calculator design

// Checker for shift_register behavior
module sr_sva (
  input logic        clk,
  input logic        areset,
  input logic        load,
  input logic        ena,
  input logic        shift_left,
  input logic [5:0]  data_in,
  input logic [3:0]  result
);
  default clocking cb @(posedge clk); endclocking
  logic past_v;
  always_ff @(posedge clk or posedge areset) begin
    if (areset) past_v <= 1'b0;
    else        past_v <= 1'b1;
  end

  // Reset dominates
  a_sr_reset:     assert property (areset |-> result == 4'h0);

  // Idle holds value
  a_sr_idle:      assert property (disable iff (areset || !past_v)
                                   (!load && !ena) |=> $stable(result));

  // Load has priority over ena
  a_sr_load:      assert property (disable iff (areset || !past_v)
                                   load |=> result == $past(data_in[3:0]));

  // Shift-left behavior
  a_sr_sleft:     assert property (disable iff (areset || !past_v)
                                   (ena && !load && shift_left)
                                   |=> result == { $past(result[2:0]), $past(data_in[5]) });

  // Shift-right behavior
  a_sr_sright:    assert property (disable iff (areset || !past_v)
                                   (ena && !load && !shift_left)
                                   |=> result == { $past(data_in[4]), $past(result[3:1]) });

  // Coverage
  c_sr_load:      cover property (disable iff (areset) load);
  c_sr_left:      cover property (disable iff (areset) ena && shift_left);
  c_sr_right:     cover property (disable iff (areset) ena && !shift_left);
endmodule


// Checker for top-level calculator composition and arithmetic datapath
module calc_sva (
  input  logic        clk,
  input  logic        areset,
  input  logic        load,
  input  logic        ena,
  input  logic [2:0]  bin_in,
  input  logic        shift_left,
  input  logic        operation,   // 0:add, 1:sub
  input  logic [3:0]  result,      // shift_register result (top-level port)
  input  logic [2:0]  bin_out,     // internal from binary_to_binary
  input  logic        o2, o1, o0,  // internal taps from binary_to_binary
  input  logic [3:0]  reg_result   // internal arithmetic register
);
  default clocking cb @(posedge clk); endclocking
  logic past_v;
  always_ff @(posedge clk or posedge areset) begin
    if (areset) past_v <= 1'b0;
    else        past_v <= 1'b1;
  end

  // Reset dominates both results
  a_calc_reset:    assert property (areset |-> (result == 4'h0 && reg_result == 4'h0));

  // Binary_to_binary must be identity
  a_b2b_id:        assert property (bin_out == bin_in && {o2,o1,o0} == bin_in);

  // No-op when neither load nor ena
  a_idle_hold:     assert property (disable iff (areset || !past_v)
                                    (!load && !ena) |=> ($stable(result) && $stable(reg_result)));

  // Load behavior
  a_rr_load:       assert property (disable iff (areset || !past_v)
                                    load |=> reg_result == {1'b0, $past(bin_out)});
  // End-to-end load mapping into shift register result
  a_sr_load_map:   assert property (disable iff (areset || !past_v)
                                    load |=> result == { $past(bin_in[0]),
                                                         $past(bin_in[2]),
                                                         $past(bin_in[1]),
                                                         $past(bin_in[0]) });

  // Addition when ena and not loading
  a_add:           assert property (disable iff (areset || !past_v)
                                    (ena && !load && (operation == 1'b0))
                                    |=> reg_result == ($past(reg_result) + {1'b0,$past(bin_out)}));

  // Subtraction when ena and not loading
  a_sub:           assert property (disable iff (areset || !past_v)
                                    (ena && !load && (operation == 1'b1))
                                    |=> reg_result == ($past(reg_result) - {1'b0,$past(bin_out)}));

  // Basic X checks when out of reset
  a_no_x:          assert property (disable iff (areset) !$isunknown({result, reg_result}));

  // Coverage
  c_reset_seq:     cover property (areset ##1 !areset ##1 load);
  c_add:           cover property (ena && !load && operation==1'b0);
  c_sub:           cover property (ena && !load && operation==1'b1);
  c_b2b_min:       cover property (bin_in == 3'h0);
  c_b2b_max:       cover property (bin_in == 3'h7);
endmodule


// Binds
bind shift_register sr_sva sr_chk (
  .clk, .areset, .load, .ena, .shift_left, .data_in, .result
);

bind calculator calc_sva calc_chk (
  .clk, .areset, .load, .ena, .bin_in, .shift_left, .operation, .result,
  .bin_out, .o2, .o1, .o0, .reg_result
);