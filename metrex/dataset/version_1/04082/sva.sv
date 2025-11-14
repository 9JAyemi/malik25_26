// SVA for emon_counter. Concise, high-quality checks and coverage.
// Bind these assertions to the DUT to verify reset, write, decrement,
// input selection, zero-flag, and wrap-around behaviors.

module emon_counter_sva #(parameter DW=32)
(
  input                clk,
  input                reset,
  input  [15:0]        emon_vector,
  input  [3:0]         emon_sel,
  input                reg_write,
  input  [DW-1:0]      reg_data,
  input  [DW-1:0]      emon_reg,
  input                emon_zero_flag,
  input                emon_input // internal flop in DUT
);

  localparam [DW-1:0] ZERO = {DW{1'b0}};
  localparam [DW-1:0] ONES = {DW{1'b1}};

  default clocking cb @(posedge clk); endclocking

  // Reset behavior: synchronous, highest priority
  a_reset_value: assert property (reset |-> emon_reg == ONES);

  // emon_input is a 1-cycle registered select of emon_vector[emon_sel]
  a_input_sampling: assert property (
    disable iff (reset)
      $past(!reset) |-> emon_input == $past(emon_vector[$past(emon_sel)])
  );

  // Write takes precedence over decrement
  a_write_precedence: assert property (
    disable iff (reset)
      $past(!reset && reg_write) |-> emon_reg == $past(reg_data)
  );

  // Decrement by emon_input (0 or 1) when no write
  a_decrement_rule: assert property (
    disable iff (reset)
      $past(!reset && !reg_write)
      |-> emon_reg == $past(emon_reg) - {{(DW-1){1'b0}}, $past(emon_input)}
  );

  // Explicit wrap-around check: 0 - 1 -> all 1's
  a_wrap_around: assert property (
    disable iff (reset)
      $past(!reset && !reg_write && emon_input && emon_reg == ZERO)
      |-> emon_reg == ONES
  );

  // Zero flag must reflect emon_reg == 0 (combinational)
  a_zero_flag_consistent: assert property (emon_zero_flag == (emon_reg == ZERO));

  // Basic X-checking on key controls during operation
  a_no_x_controls: assert property (
    disable iff (reset)
      !$isunknown({reg_write, emon_sel, emon_input})
  );

  // Coverage

  // See a write followed by correct load
  c_write: cover property (
    disable iff (reset)
      reg_write ##1 (emon_reg == $past(reg_data))
  );

  // See a decrement by 1
  c_decrement: cover property (
    disable iff (reset)
      $past(!reg_write && emon_input) && (emon_reg == $past(emon_reg) - 1)
  );

  // See a hold (emon_input=0, no write)
  c_hold: cover property (
    disable iff (reset)
      $past(!reg_write && !emon_input) && (emon_reg == $past(emon_reg))
  );

  // Reach zero and assert zero flag via decrement
  c_zero_reached: cover property (
    disable iff (reset)
      $past(!reg_write && emon_input && emon_reg == {{(DW-1){1'b0}},1'b1})
      ##1 emon_zero_flag
  );

  // Wrap-around from 0 to all 1's on decrement
  c_wrap: cover property (
    disable iff (reset)
      $past(!reg_write && emon_input && emon_reg == ZERO)
      ##1 (emon_reg == ONES)
  );

  // Exercise all 16 selections and observe correct sampled value one cycle later
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : C_SEL
      c_each_sel: cover property (
        disable iff (reset)
          $past(emon_sel) == i ##1 (emon_input == $past(emon_vector[i]))
      );
    end
  endgenerate

endmodule

// Bind to the DUT (accessing internal emon_input)
bind emon_counter emon_counter_sva #(.DW(DW)) emon_counter_sva_i (
  .clk(clk),
  .reset(reset),
  .emon_vector(emon_vector),
  .emon_sel(emon_sel),
  .reg_write(reg_write),
  .reg_data(reg_data),
  .emon_reg(emon_reg),
  .emon_zero_flag(emon_zero_flag),
  .emon_input(emon_input)
);