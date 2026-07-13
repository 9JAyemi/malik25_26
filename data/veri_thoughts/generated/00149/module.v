
module subtractor (
  input [8:0] count_d2_reg,
  input [3:0] S,
  input wr_clk,
  input AR,
  output reg [9:0] wr_data_count
);

  wire [3:0] constant_value;
  assign constant_value = 4'd10 - (S * 10);

  wire [8:0] subtracted_value;
  assign subtracted_value = count_d2_reg - constant_value;

  always @(posedge wr_clk or negedge AR) begin
    if (!AR) begin
      wr_data_count <= 0;
    end else begin
      wr_data_count <= {1'b0, subtracted_value};
    end
  end

endmodule
