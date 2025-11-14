module FSM #(
  parameter n = 4, // number of input signals
  parameter m = 2 // number of output signals
)(
  input [n-1:0] in,
  input clk,
  output reg [m-1:0] out
);

parameter s_new = 1; // new state encoding

// Define the states using the original state encoding
parameter STATE_A = 2'b00;
parameter STATE_B = 2'b01;
parameter STATE_C = 2'b10;
parameter STATE_D = 2'b11;

reg [1:0] current_state, next_state;
always @* begin
  next_state = (current_state == STATE_A && in[0]) ? STATE_B :
               (current_state == STATE_A && !in[0]) ? STATE_C :
               (current_state == STATE_B && in[1]) ? STATE_D :
               (current_state == STATE_B && !in[1]) ? STATE_A :
               (current_state == STATE_C && in[2]) ? STATE_A :
               (current_state == STATE_C && !in[2]) ? STATE_D :
               (current_state == STATE_D && in[3]) ? STATE_C :
               (current_state == STATE_D && !in[3]) ? STATE_B :
               current_state;
end

// Define the outputs based on the current state and the new state encoding
always @* begin
  case (current_state)
    STATE_A: out = {s_new == 1 ? 1'b1 : 2'b01, s_new == 1 ? 1'b0 : 2'b10};
    STATE_B: out = {s_new == 1 ? 1'b0 : 2'b10, s_new == 1 ? 1'b1 : 2'b01};
    STATE_C: out = {s_new == 1 ? 1'b1 : 2'b10, s_new == 1 ? 1'b1 : 2'b10};
    STATE_D: out = {s_new == 1 ? 1'b0 : 2'b10, s_new == 1 ? 1'b0 : 2'b10};
  endcase
end

// Define the state register and the next state logic
always @ (posedge clk) begin
  current_state <= next_state;
end

endmodule