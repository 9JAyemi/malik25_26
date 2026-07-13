module FSM_assertions (
  input logic clk,
  input logic rst,
  input logic [1:0] in,
  output logic [0:0] out
);
  parameter S0 = 2'b00;
  parameter S1 = 2'b01;
  parameter S2 = 2'b10;
  parameter S3 = 2'b11;

  parameter I0 = 2'b00;
  parameter I1 = 2'b01;
  parameter I2 = 2'b10;
  parameter I3 = 2'b11;

  parameter O0 = 1'b0;
  parameter O1 = 1'b1;

  // At reset, the state should be S0 and out should be O0
  reset: assert property (
    @(posedge clk) !rst |-> (state == S0) && (out == O0)
  );

  // State transitions based on input
  state_transition_S0: assert property (
    @(posedge clk) disable iff (!rst) (state == S0) |-> (in == I0) |-> (state == S1) && (out == O0)
  );
  state_transition_S0: assert property (
    @(posedge clk) disable iff (!rst) (state == S0) |-> (in == I1) |-> (state == S2) && (out == O1)
  );
  state_transition_S1: assert property (
    @(posedge clk) disable iff (!rst) (state == S1) |-> (in == I0) |-> (state == S2) && (out == O0)
  );
  state_transition_S1: assert property (
    @(posedge clk) disable iff (!rst) (state == S1) |-> (in == I1) |-> (state == S3) && (out == O1)
  );
  state_transition_S2: assert property (
    @(posedge clk) disable iff (!rst) (state == S2) |-> (in == I0) |-> (state == S3) && (out == O0)
  );
  state_transition_S2: assert property (
    @(posedge clk) disable iff (!rst) (state == S2) |-> (in == I1) |-> (state == S0) && (out == O1)
  );
  state_transition_S3: assert property (
    @(posedge clk) disable iff (!rst) (state == S3) |-> (in == I0) |-> (state == S0) && (out == O0)
  );
  state_transition_S3: assert property (
    @(posedge clk) disable iff (!rst) (state == S3) |-> (in == I1) |-> (state == S1) && (out == O1)
  );

  // Output should be O0 when in is I0 and state is S0
  output_S0_I0: assert property (
    @(posedge clk) disable iff (!rst) (state == S0) && (in == I0) |-> (out == O0)
  );

  // Output should be O1 when in is I1 and state is S0
  output_S0_I1: assert property (
    @(posedge clk) disable iff (!rst) (state == S0) && (in == I1) |-> (out == O1)
  );

  // Output should be O0 when in is I0 and state is S1
  output_S1_I0: assert property (
    @(posedge clk) disable iff (!rst) (state == S1) && (in == I0) |-> (out == O0)
  );

  // Output should be O1 when in is I1 and state is S1
  output_S1_I1: assert property (
    @(posedge clk) disable iff (!rst) (state == S1) && (in == I1) |-> (out == O1)
  );

  // Output should be O0 when in is I0 and state is S2
  output_S2_I0: assert property (
    @(posedge clk) disable iff (!rst) (state == S2) && (in == I0) |-> (out == O0)
  );

  // Output should be O1 when in is I1 and state is S2
  output_S2_I1: assert property (
    @(posedge clk) disable iff (!rst) (state == S2) && (in == I1) |-> (out == O1)
  );

  // Output should be O0 when in is I0 and state is S3
  output_S3_I0: assert property (
    @(posedge clk) disable iff (!rst) (state == S3) && (in == I0) |-> (out == O0)
  );

  // Output should be O1 when in is I1 and state is S3
  output_S3_I1: assert property (
    @(posedge clk) disable iff (!rst) (state == S3) && (in == I1) |-> (out == O1)
  );
endmodule