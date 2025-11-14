module johnson_counter (
  input clock,
  output [n-1:0] out
);

parameter n = 4; // number of output signals

reg [n-1:0] shift_reg;
wire [n-1:0] next_state;

assign next_state[0] = shift_reg[n-1] ^ shift_reg[n-2];
assign next_state[n-1] = shift_reg[n-2] ^ shift_reg[n-3];

genvar i;
generate
  for (i = 1; i < n-1; i = i+1) begin
    assign next_state[i] = shift_reg[i-1] ^ shift_reg[i] ^ shift_reg[i+1];
  end
endgenerate

always @(posedge clock) begin
  shift_reg <= next_state;
end

assign out = shift_reg;

endmodule