// SVA for sequence_detector and combined_module
// Focused, high-quality checks and minimal but meaningful coverage.

module sequence_detector_sva (
  input logic         clk,
  input logic         reset,
  input logic [35:0]  in,
  input logic [3:0]   sequence_detected,
  input logic [31:0]  change_detection,
  // internal
  input logic [35:0]  shift_reg,
  input logic [3:0]   sequence_detected_reg,
  input logic [31:0]  change_detection_reg,
  input logic [31:0]  change_detection_output
);
  default clocking cb @(posedge clk); endclocking

  // Reset brings all state regs to 0 on next clock
  assert property (reset |=> (shift_reg==36'b0 && sequence_detected_reg==4'b0 && change_detection_reg==32'b0));

  // Outputs mirror regs
  assert property (sequence_detected == sequence_detected_reg);
  assert property (change_detection  == change_detection_reg);

  // State update: shift_reg loads previous 'in' (per RTL)
  assert property (disable iff (reset) shift_reg == $past(in));

  // Sequence detect timing: depends on previous shift_reg[35:32]
  assert property (disable iff (reset) ($past(shift_reg[35:32])==4'b1010) |-> (sequence_detected_reg==4'b1010));
  assert property (disable iff (reset) ($past(shift_reg[35:32])!=4'b1010) |-> (sequence_detected_reg==4'b0000));

  // change_detection combinational form is masked to low nibble only
  assert property (change_detection_output[31:4]==28'b0);
  assert property (disable iff (reset)
                   change_detection_reg[31:4]==28'b0);

  // change_detection_reg value (accounts for NBA + comb wiring)
  // Uses current in, previous shift_reg and previous sequence_detected_reg
  assert property (disable iff (reset)
    change_detection_reg
      == (((in ^ $past(shift_reg[35:2]))[31:0]) & {28'b0, $past(sequence_detected_reg)}));

  // No X/Z on visible outputs
  assert property (!$isunknown({sequence_detected, change_detection}));

  // Minimal but meaningful coverage
  cover property (disable iff (reset) ($past(shift_reg[35:32])==4'b1010) && sequence_detected_reg==4'b1010);
  cover property (disable iff (reset) (sequence_detected_reg==4'b1010) && (change_detection_reg!=32'b0));
  cover property (disable iff (reset) (sequence_detected_reg==4'b0000));

endmodule

bind sequence_detector sequence_detector_sva i_sequence_detector_sva (
  .clk(clk),
  .reset(reset),
  .in(in),
  .sequence_detected(sequence_detected),
  .change_detection(change_detection),
  .shift_reg(shift_reg),
  .sequence_detected_reg(sequence_detected_reg),
  .change_detection_reg(change_detection_reg),
  .change_detection_output(change_detection_output)
);


// SVA for combined_module (checks composition and truncation behavior)
module combined_module_sva (
  input logic         clk,
  input logic         reset,
  input logic [35:0]  in,
  input logic [31:0]  out,
  // internal wires from instance
  input logic [3:0]   sequence_detected,
  input logic [31:0]  change_detection
);
  default clocking cb @(posedge clk); endclocking

  // out is 32 LSBs of ((in ^ change_detection_ext) | (({0,seq})<<28))
  // Equivalent to:
  assert property (out == ((in[31:0] ^ change_detection[31:0]) | (sequence_detected << 28)));

  // Decompose for clarity
  assert property (out[27:0]  == (in[27:0]  ^ change_detection[27:0]));
  assert property (out[31:28] == ((in[31:28] ^ change_detection[31:28]) | sequence_detected));

  // Visible interface clean
  assert property (!$isunknown(out));

  // Coverage: detected nibble shows up in out
  cover property (disable iff (reset) (sequence_detected==4'b1010) && (out[31:28]==4'b1010));

endmodule

bind combined_module combined_module_sva i_combined_module_sva (
  .clk(clk),
  .reset(reset),
  .in(in),
  .out(out),
  .sequence_detected(sequence_detected),
  .change_detection(change_detection)
);