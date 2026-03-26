
module twos_complement(input [15:0] in, input reset, output reg [31:0] out);

  always @(*) begin
    if (reset) begin
      out <= 0;
    end
    else begin
      out <= {16'b0, in, {16{!in[15]}}};  // Add leading 16'b0 to match the output width
    end
  end

endmodule
