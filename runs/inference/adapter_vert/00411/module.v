module lfsr_counter #(
    parameter SIZE = 4
)(
  input clk, reset, ena,
  output [SIZE-1:0] out
);
  reg [SIZE-1:0] state;
  always @(posedge clk or negedge reset)
    begin
      if(!reset)
        state <= 0;
      else if(ena)
        state <= {state[SIZE-2:0], state[SIZE-1]^state[SIZE-2]};
    end
  assign out = state;
endmodule