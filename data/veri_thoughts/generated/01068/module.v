module ring_counter #(
  parameter n = 4 // number of states in the ring counter
) (
  input clk,
  output [n-1:0] out
);


reg [n-1:0] state; // register to hold the current state

always @(posedge clk) begin
  state <= state + 1; // increment the state on each clock cycle
  if (state == n) begin
    state <= 0; // reset the state to 0 when it reaches n
  end
end

assign out = (state == {n{1'b1}}) ? {n{1'b1}} : (1 << state); // generate the output signals

endmodule