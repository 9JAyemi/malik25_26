module reverse_bits (
  input [7:0] input_vector,
  output reg [7:0] output_vector
);

  reg [7:0] temp_vector;
  integer i;

  always @(*) begin
    if (input_vector == 8'b00000000) begin
      output_vector = 8'b00000000;
    end else begin
      for (i = 0; i < 8; i = i + 1) begin
        temp_vector[i] = input_vector[7 - i];
      end
      output_vector = temp_vector;
    end
  end

endmodule
