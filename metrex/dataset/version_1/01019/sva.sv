// SVA checker for barrel_shift_3bit_reg_and_gate
// Bind into DUT to observe internal regs: shifted_data, reg_data

module barrel_shift_3bit_reg_and_gate_sva (
  input logic        clk,
  input logic [3:0]  data_in,
  input logic [1:0]  shift_amount,
  input logic [2:0]  parallel_load,
  input logic        shift,
  input logic        control,
  input logic [2:0]  out,
  input logic [3:0]  shifted_data, // internal
  input logic [2:0]  reg_data      // internal
);

  default clocking cb @(posedge clk); endclocking

  // Guard for $past at time 0
  bit past_valid;
  initial past_valid = 0;
  always_ff @(posedge clk) past_valid <= 1;

  // 4-bit barrel-rotate-left reference model
  function automatic logic [3:0] rotl4 (logic [3:0] din, logic [1:0] sh);
    case (sh)
      2'd0: rotl4 = din;
      2'd1: rotl4 = {din[2:0], din[3]};
      2'd2: rotl4 = {din[1:0], din[3:2]};
      2'd3: rotl4 = {din[0],   din[3:1]};
    endcase
  endfunction

  // Combinational barrel shifter must match rotate-left
  assert property (shifted_data == rotl4(data_in, shift_amount))
    else $error("shifted_data != barrel rotate-left(data_in, shift_amount)");

  // AND gate width/truncation: out uses only lower 3 bits of shifted_data
  assert property (out == (shifted_data[2:0] & reg_data))
    else $error("out mismatch: expected shifted_data[2:0] & reg_data");

  // Shift-register next-state checks (priority: shift over parallel load)
  // Shift left (insert 0 at LSB)
  assert property (disable iff (!past_valid)
                   shift && control |=> reg_data == { $past(reg_data)[1:0], 1'b0 })
    else $error("reg_data left-shift next-state mismatch");

  // Shift right (insert 0 at MSB)
  assert property (disable iff (!past_valid)
                   shift && !control |=> reg_data == { 1'b0, $past(reg_data)[2:1] })
    else $error("reg_data right-shift next-state mismatch");

  // Parallel load when enabled (parallel_load != 3'b111) and not shifting
  assert property (disable iff (!past_valid)
                   !shift && (parallel_load != 3'b111) |=> reg_data == $past(parallel_load))
    else $error("reg_data parallel-load next-state mismatch");

  // Hold when neither shift nor load
  assert property (disable iff (!past_valid)
                   !shift && (parallel_load == 3'b111) |=> reg_data == $past(reg_data))
    else $error("reg_data should hold value when no shift and load disabled");

  // Post-shift inserted zeros (redundant but crisp)
  assert property (disable iff (!past_valid)
                   shift && control |=> reg_data[0] == 1'b0)
    else $error("LSB must be 0 after left shift");
  assert property (disable iff (!past_valid)
                   shift && !control |=> reg_data[2] == 1'b0)
    else $error("MSB must be 0 after right shift");

  // Basic functional coverage
  cover property (shift && control);            // left shift event
  cover property (shift && !control);           // right shift event
  cover property (!shift && parallel_load != 3'b111); // parallel load event
  cover property (!shift && parallel_load == 3'b111); // hold event

  cover property (shift_amount == 2'd0);
  cover property (shift_amount == 2'd1);
  cover property (shift_amount == 2'd2);
  cover property (shift_amount == 2'd3);

  cover property (out == 3'b000);
  cover property (out == 3'b111);

endmodule

// Bind into the DUT (add this once in your TB)
bind barrel_shift_3bit_reg_and_gate
  barrel_shift_3bit_reg_and_gate_sva u_sva (.*);