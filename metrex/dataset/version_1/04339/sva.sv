// SVA checker for barrel_shifter_16bit
module barrel_shifter_16bit_sva (
  input  logic [15:0] data,
  input  logic [3:0]  shift_amount,
  input  logic [15:0] shifted_data,
  // internal pipeline taps
  input  logic [15:0] stage1_data,
  input  logic [15:0] stage2_data,
  input  logic [15:0] stage3_data,
  input  logic [15:0] stage4_data
);

  function automatic logic [15:0] ref_shift(input logic [15:0] d, input logic [3:0] sa);
    ref_shift = d >> sa;
  endfunction

  // Knownness: known inputs -> all internals and outputs known
  assert property (@(data or shift_amount or stage1_data or stage2_data or stage3_data or stage4_data or shifted_data)
                   !$isunknown({data, shift_amount}) |-> ##0 !$isunknown({stage1_data, stage2_data, stage3_data, stage4_data, shifted_data}));

  // Internal pipeline consistency (matches RTL intent)
  assert property (@(data or shift_amount or stage1_data)
                   !$isunknown({data, shift_amount}) |-> ##0 (stage1_data == data));
  assert property (@(data or shift_amount or stage1_data or stage2_data)
                   !$isunknown({data, shift_amount}) |-> ##0 (stage2_data == (stage1_data >> {2'b00, shift_amount[1:0]})));
  assert property (@(data or shift_amount or stage2_data or stage3_data)
                   !$isunknown({data, shift_amount}) |-> ##0 (stage3_data == (stage2_data >> {shift_amount[3:2], 2'b00})));
  assert property (@(data or shift_amount or stage3_data or stage4_data)
                   !$isunknown({data, shift_amount}) |-> ##0 (stage4_data == (stage3_data >> {shift_amount[3:2], 2'b00})));
  assert property (@(data or shift_amount or stage4_data or shifted_data)
                   !$isunknown({data, shift_amount}) |-> ##0 (shifted_data == {stage4_data[7:0], stage4_data[15:8]}));

  // End-to-end golden check: pure logical right shift by shift_amount (zero-fill)
  assert property (@(data or shift_amount or shifted_data)
                   !$isunknown({data, shift_amount}) |-> ##0 (shifted_data == ref_shift(data, shift_amount)));

  // Key corners
  assert property (@(data or shift_amount)
                   !$isunknown({data, shift_amount}) && (shift_amount == 4'd0) |-> ##0 (shifted_data == data));
  assert property (@(data or shift_amount)
                   !$isunknown({data, shift_amount}) && (shift_amount == 4'd15) |-> ##0 (shifted_data == {15'b0, data[15]}));

  // Functional coverage
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : cov_sa
      cover property (@(shift_amount) ##0 (shift_amount == i));
    end
  endgenerate
  cover property (@(data) ##0 (data == 16'h0000));
  cover property (@(data) ##0 (data == 16'hFFFF));
  cover property (@(data) ##0 $onehot(data));

endmodule

// Bind into DUT (connects to both ports and internal regs)
bind barrel_shifter_16bit barrel_shifter_16bit_sva u_barrel_shifter_16bit_sva (
  .data(data),
  .shift_amount(shift_amount),
  .shifted_data(shifted_data),
  .stage1_data(stage1_data),
  .stage2_data(stage2_data),
  .stage3_data(stage3_data),
  .stage4_data(stage4_data)
);