
module seq_detector (
  input in,
  output reg out,
  input clk
);

parameter state0 = 2'b00; // initial state
parameter state1 = 2'b01; // intermediate state
parameter state2 = 2'b10; // final state

reg [1:0] state, next_state;

// define transitions between states
always @(*) begin
  case (state)
    state0: if (in == 1'b0) next_state <= state0; else next_state <= state1;
    state1: if (in == 1'b0) next_state <= state0; else next_state <= state2;
    state2: if (in == 1'b0) next_state <= state0; else next_state <= state2;
    default: next_state <= state0;
  endcase
end

// update state
always @(posedge clk) begin
  state <= next_state;
end

// define output signal
always @(*) begin
  out = (state == state2);
end

// reset state
initial begin
  state <= state0;
end

endmodule