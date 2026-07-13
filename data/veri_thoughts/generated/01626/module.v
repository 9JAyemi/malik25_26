module check_1fs (
  input [31:0] timeunit,
  input [31:0] timeprecision,
  output reg is_1fs
);

  always @(*) begin
    if (timeunit == 1 && timeprecision == 1) begin
      is_1fs <= 1'b1;
    end else begin
      is_1fs <= 1'b0;
    end
  end

endmodule