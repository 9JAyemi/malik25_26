module clock_reset_gen (
  input clk_in,
  input rst_in,
  output reg clk_out,
  output reg rst_out
);

  reg [31:0] counter = 0;

  always @(posedge clk_in) begin
    counter <= counter + 1;
    if (counter == 1) begin
      clk_out <= 1;
    end else if (counter == 2) begin
      clk_out <= 0;
      counter <= 0;
    end
  end

  always @(posedge clk_out) begin
    if (rst_in) begin
      rst_out <= 1;
    end else begin
      rst_out <= 0;
    end
  end

endmodule