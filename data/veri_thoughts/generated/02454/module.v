module capture_transition (
  input clk,
  input reset,
  input [31:0] input_vector,
  output [31:0] output_vector
);

reg [31:0] prev_vector;
reg [31:0] transition_vector;

always @(posedge clk) begin
  if (reset) begin
    prev_vector <= 32'h0;
    transition_vector <= 32'h0;
  end
  else begin
    prev_vector <= input_vector;
    transition_vector <= ((~input_vector) & prev_vector);
  end
end

assign output_vector = transition_vector;

endmodule
