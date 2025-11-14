// SVA for wire_connection + priority_encoder + voting_circuit
// Bind into voting_circuit to check end-to-end and internals

module voting_circuit_sva (
  input logic        clk,
  input logic        reset,
  input logic [2:0]  data_in1,
  input logic [2:0]  data_in2,
  input logic [2:0]  data_in3,
  input logic [3:0]  wire_out,       // internal
  input logic [2:0]  encoder_out,    // internal
  input logic [2:0]  final_output
);
  default clocking cb @(posedge clk); endclocking

  // Static width sanity (should fail with current DUT: 9 != 4)
  localparam int CAT_W = $bits({data_in3, data_in2, data_in1});
  localparam int WO_W  = $bits(wire_out);
  initial begin
    assert (CAT_W == WO_W)
      else $error("wire_connection width mismatch: %0d != %0d", CAT_W, WO_W);
  end

  // Actual wire mapping enforced by truncation
  assert property (cb wire_out[2:0] === data_in1)
    else $error("wire_out[2:0] != data_in1 (truncation mismatch)");
  assert property (cb wire_out[3]   === data_in2[0])
    else $error("wire_out[3] != data_in2[0] (truncation mismatch)");

  // Priority encoder is MSB-first: index == highest set bit, else 0
  assert property (cb encoder_out == (wire_out[3] ? 3 :
                                      wire_out[2] ? 2 :
                                      wire_out[1] ? 1 : 0))
    else $error("priority_encoder mismatch");

  // Encoder output range
  assert property (cb encoder_out inside {[0:3]})
    else $error("encoder_out out of range");

  // Synchronous reset
  assert property (cb reset |-> ##0 (final_output == 3'b000))
    else $error("final_output not cleared on reset");

  // Voting select behavior
  assert property (cb disable iff (reset) (encoder_out==0) |-> ##0 (final_output === data_in1))
    else $error("final_output != data_in1 when encoder_out==0");
  assert property (cb disable iff (reset) (encoder_out==1) |-> ##0 (final_output === data_in2))
    else $error("final_output != data_in2 when encoder_out==1");
  assert property (cb disable iff (reset) (encoder_out==2) |-> ##0 (final_output === data_in3))
    else $error("final_output != data_in3 when encoder_out==2");
  assert property (cb disable iff (reset) (encoder_out==3) |-> ##0 (final_output === 3'b000))
    else $error("final_output not 0 when encoder_out==3");

  // Functional coverage
  cover property (cb !reset && (encoder_out==0) ##0 (final_output===data_in1));
  cover property (cb !reset && (encoder_out==1) ##0 (final_output===data_in2));
  cover property (cb !reset && (encoder_out==2) ##0 (final_output===data_in3));
  cover property (cb !reset && (encoder_out==3) ##0 (final_output===3'b000));
endmodule

bind voting_circuit voting_circuit_sva i_voting_circuit_sva(
  .clk(clk),
  .reset(reset),
  .data_in1(data_in1),
  .data_in2(data_in2),
  .data_in3(data_in3),
  .wire_out(wire_out),
  .encoder_out(encoder_out),
  .final_output(final_output)
);