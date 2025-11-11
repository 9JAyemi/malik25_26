module async_reset_release (
  input clk,
  input rst,
  input in,
  output out
);

  reg out_reg; // register to hold the output value

  always @(posedge clk) begin
    if (rst) begin // reset state
      out_reg <= 0;
    end else begin // release state
      out_reg <= in;
    end
  end

  assign out = out_reg;

endmodule