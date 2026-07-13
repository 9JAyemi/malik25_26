module mem_encryption (
  input clk,
  input reset,
  input [31:0] data_in,
  input [31:0] key,
  output reg [31:0] data_out
);

  reg [31:0] internal_state;

  always @(posedge clk) begin
    if (reset) begin
      internal_state <= 0;
      data_out <= 0;
    end else begin
      if (key == 0) begin
        data_out <= data_in;
      end else begin
        internal_state <= data_in ^ key;
        data_out <= internal_state ^ key;
      end
    end
  end

endmodule