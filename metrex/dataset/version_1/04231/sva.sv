// SystemVerilog Assertions (SVA) for the provided design.
// Concise, priority-accurate checks with key covers. Bind as shown below.

// ---------------------------
// shift_register_3 SVA
// ---------------------------
module shift_register_3_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [2:0]  data_in,
  input  logic        shift,
  input  logic [2:0]  data_out
);
  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Reset wins
  a_reset: assert property (@(posedge clk) reset |=> (data_out == 3'b000));

  // Functional step: shift injects data_in[2], left-shift data_out
  a_shift: assert property (@(posedge clk)
                            disable iff (!past_valid || reset)
                            shift |=> data_out == { $past(data_out[1:0]), $past(data_in[2]) });

  // Hold when no shift
  a_hold:  assert property (@(posedge clk)
                            disable iff (!past_valid || reset)
                            !shift |=> data_out == $past(data_out));

  // Basic covers
  c_reset:  cover property (@(posedge clk) reset);
  c_3shifts: cover property (@(posedge clk) disable iff (reset) shift ##1 shift ##1 shift);
  c_hold:    cover property (@(posedge clk) disable iff (reset) !shift);
endmodule

bind shift_register_3 shift_register_3_sva i_shift_register_3_sva (
  .clk(clk), .reset(reset), .data_in(data_in), .shift(shift), .data_out(data_out)
);


// ---------------------------
// shift_register_8 SVA
// ---------------------------
module shift_register_8_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [7:0]  data_in,
  input  logic        shift,
  input  logic [7:0]  data_out
);
  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Reset wins
  a_reset: assert property (@(posedge clk) reset |=> (data_out == 8'h00));

  // Functional step: shift injects data_in[7], left-shift data_out
  a_shift: assert property (@(posedge clk)
                            disable iff (!past_valid || reset)
                            shift |=> data_out == { $past(data_out[6:0]), $past(data_in[7]) });

  // Hold when no shift
  a_hold:  assert property (@(posedge clk)
                            disable iff (!past_valid || reset)
                            !shift |=> data_out == $past(data_out));

  // Basic covers
  c_reset:   cover property (@(posedge clk) reset);
  c_3shifts: cover property (@(posedge clk) disable iff (reset) shift ##1 shift ##1 shift);
  c_hold:    cover property (@(posedge clk) disable iff (reset) !shift);
endmodule

bind shift_register_8 shift_register_8_sva i_shift_register_8_sva (
  .clk(clk), .reset(reset), .data_in(data_in), .shift(shift), .data_out(data_out)
);


// ---------------------------
// binary_counter SVA
// ---------------------------
module binary_counter_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        enable,
  input  logic        load,
  input  logic [7:0]  data,
  input  logic [2:0]  count,

  // Internal nets from DUT scope
  input  logic [2:0]  shift_reg_out,
  input  logic [7:0]  shift_reg_8_out
);
  bit past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Reset wins over everything
  a_reset: assert property (@(posedge clk) reset |=> (count == 3'd0));

  // Load has priority over enable; loads current shift_reg_8_out[2:0] (pre-update value)
  a_load:  assert property (@(posedge clk)
                            disable iff (!past_valid || reset)
                            load |=> count == $past(shift_reg_8_out[2:0]));

  // Increment when enabled and not loading (3-bit wrap)
  a_inc:   assert property (@(posedge clk)
                            disable iff (!past_valid || reset)
                            (!load && enable) |=> count == (($past(count) + 3'd1) & 3'h7));

  // Hold otherwise
  a_hold:  assert property (@(posedge clk)
                            disable iff (!past_valid || reset)
                            (!load && !enable) |=> count == $past(count));

  // Coverage: wrap, load-while-enable, reset->run
  c_wrap:  cover property (@(posedge clk)
                           disable iff (reset)
                           (count == 3'd7) && enable && !load |=> (count == 3'd0));
  c_load_en: cover property (@(posedge clk)
                             disable iff (reset)
                             load && enable);
  c_reset_run: cover property (@(posedge clk)
                               reset ##1 !reset ##1 enable);
endmodule

bind binary_counter binary_counter_sva i_binary_counter_sva (
  .clk(clk),
  .reset(reset),
  .enable(enable),
  .load(load),
  .data(data),
  .count(count),
  .shift_reg_out(shift_reg_out),
  .shift_reg_8_out(shift_reg_8_out)
);