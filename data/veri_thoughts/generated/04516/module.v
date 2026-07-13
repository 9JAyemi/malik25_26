
module ring_counter #(
  parameter n = 4 // number of states
)(
  input clk,
  output [n-1:0] out
);

// define the sequence of states
reg [n-1:0] states;
wire [n-1:0] next_states;

assign next_states = {states[n-2:0], states[n-1]};

always @(posedge clk) begin
  states <= next_states; // moved the register assignment inside the always block
end

assign out = states; // moved the out assignment outside of the always block

endmodule
