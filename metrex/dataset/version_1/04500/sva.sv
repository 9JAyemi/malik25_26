// SVA for s5: concise, high-quality checks and coverage
// Bindable checker; no DUT modifications required.

module s5_assertions (
  input  logic [5:0] stage1_input,
  input  logic [3:0] stage1_output
);

  // Golden LUT (S5) as per DUT case statement
  localparam logic [3:0] LUT [0:63] = '{
    4'd2,  4'd14, 4'd12, 4'd11, 4'd4,  4'd2,  4'd1,  4'd12,
    4'd7,  4'd4,  4'd10, 4'd7,  4'd11, 4'd13, 4'd6,  4'd1,
    4'd8,  4'd5,  4'd5,  4'd0,  4'd3,  4'd15, 4'd15, 4'd10,
    4'd13, 4'd3,  4'd0,  4'd9,  4'd14, 4'd8,  4'd9,  4'd6,
    4'd4,  4'd11, 4'd2,  4'd8,  4'd1,  4'd12, 4'd11, 4'd7,
    4'd10, 4'd1,  4'd13, 4'd14, 4'd7,  4'd2,  4'd8,  4'd13,
    4'd15, 4'd6,  4'd9,  4'd15, 4'd12, 4'd0,  4'd5,  4'd9,
    4'd6,  4'd10, 4'd3,  4'd4,  4'd0,  4'd5,  4'd14, 4'd3
  };

  // 1) Inputs must be known whenever they change
  assert property (@(stage1_input) !$isunknown(stage1_input))
    else $error("s5: stage1_input has X/Z");

  // 2) Output must be known after combinational settle (next delta)
  assert property (@(stage1_input) ##0 !$isunknown(stage1_output))
    else $error("s5: stage1_output has X/Z");

  // 3) Functional equivalence to golden LUT (zero-cycle comb latency)
  assert property (@(stage1_input) disable iff ($isunknown(stage1_input))
                   ##0 (stage1_output == LUT[stage1_input]))
    else $error("s5: output mismatch: in=%0d exp=%0d got=%0d",
                stage1_input, LUT[stage1_input], stage1_output);

  // 4) Output may only change when input changes (no spurious glitches driven by DUT)
  assert property (@(stage1_output) $changed(stage1_output) |-> $changed(stage1_input))
    else $error("s5: stage1_output changed without stage1_input change");

  // Functional coverage: see all inputs and all outputs
  covergroup cg_s5 @(stage1_input);
    cp_in  : coverpoint stage1_input { bins all[] = {[0:63]}; }
    cp_out : coverpoint stage1_output { bins all[] = {[0:15]}; }
  endgroup
  cg_s5 cg = new();

endmodule

// Bind into all instances of s5
bind s5 s5_assertions s5_sva_i (.*);