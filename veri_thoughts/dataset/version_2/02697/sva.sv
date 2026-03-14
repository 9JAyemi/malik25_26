module priority_encoder_sva (
  input logic clk,
  input logic reset,
  input logic [3:0] in,
  input logic [1:0] out,
  input logic valid
);

  ///// Reset behavior /////
  // While reset is asserted low, outputs are cleared.
  reset_outputs_cleared: assert property (
    @(posedge clk) !reset |-> (out == 2'b00) && (valid == 1'b0)
  );

  ///// Encoding from inputs (uses previous cycle inputs due to registered outputs) /////
  // If in[3] was 1, out must be 3 and valid 1.
  encode_in3_maps_to_3: assert property (
    @(posedge clk) disable iff (!reset) ($past(reset) && $past(in[3])) |-> (out == 2'b11) && (valid == 1'b1)
  );
  // If in[2] was 1 and in[3] was 0, out must be 2 and valid 1.
  encode_in2_maps_to_2: assert property (
    @(posedge clk) disable iff (!reset) ($past(reset) && !$past(in[3]) && $past(in[2])) |-> (out == 2'b10) && (valid == 1'b1)
  );
  // If in[1] was 1 and in[3:2] were 0, out must be 1 and valid 1.
  encode_in1_maps_to_1: assert property (
    @(posedge clk) disable iff (!reset) ($past(reset) && !$past(in[3]) && !$past(in[2]) && $past(in[1])) |-> (out == 2'b01) && (valid == 1'b1)
  );
  // If only in[0] was 1 among higher bits 3:1=0, out must be 0 and valid 1.
  encode_in0_maps_to_0: assert property (
    @(posedge clk) disable iff (!reset) ($past(reset) && !$past(in[3]) && !$past(in[2]) && !$past(in[1]) && $past(in[0])) |-> (out == 2'b00) && (valid == 1'b1)
  );
  // If no inputs were 1, out must be 0 and valid 0.
  encode_none_maps_to_none: assert property (
    @(posedge clk) disable iff (!reset) ($past(reset) && ($past(in) == 4'b0000)) |-> (out == 2'b00) && (valid == 1'b0)
  );

  ///// Valid flag semantics /////
  // valid equals OR-reduction of previous cycle inputs.
  valid_equals_or_prev_in: assert property (
    @(posedge clk) disable iff (!reset) $past(reset) |-> (valid == (|$past(in)))
  );
  // When valid is 0, out must be 0.
  valid_zero_implies_out_zero: assert property (
    @(posedge clk) disable iff (!reset) (valid == 1'b0) |-> (out == 2'b00)
  );

  ///// Reverse mapping checks (outputs imply prior inputs) /////
  // out==3 implies prior in[3]==1.
  out3_implies_prev_in3: assert property (
    @(posedge clk) disable iff (!reset) ($past(reset) && (out == 2'b11)) |-> $past(in[3])
  );
  // out==2 implies prior in[3]==0 and in[2]==1.
  out2_implies_prev_in2_only: assert property (
    @(posedge clk) disable iff (!reset) ($past(reset) && (out == 2'b10)) |-> (!$past(in[3]) && $past(in[2]))
  );
  // out==1 implies prior in[3:2]==0 and in[1]==1.
  out1_implies_prev_in1_only: assert property (
    @(posedge clk) disable iff (!reset) ($past(reset) && (out == 2'b01)) |-> (!$past(in[3]) && !$past(in[2]) && $past(in[1]))
  );
  // out==0 with valid==1 implies prior in[3:1]==0 and in[0]==1.
  out0_valid1_implies_prev_in0_only: assert property (
    @(posedge clk) disable iff (!reset) ($past(reset) && (out == 2'b00) && (valid == 1'b1)) |-> (!$past(in[3]) && !$past(in[2]) && !$past(in[1]) && $past(in[0]))
  );
  // out==0 with valid==0 implies prior inputs were all zero.
  out0_valid0_implies_prev_none: assert property (
    @(posedge clk) disable iff (!reset) ($past(reset) && (out == 2'b00) && (valid == 1'b0)) |-> ($past(in) == 4'b0000)
  );

endmodule