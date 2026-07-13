module arr (
  input clk,
  input duv_rst_ip,
  output reg [31:0] out
);

  reg [31:0] counter = 0;

  always @(posedge clk) begin
    if (duv_rst_ip) begin
      counter <= 0;
    end else begin
      counter <= counter + 1;
    end
  end
  
  always @* begin
    out = counter;
  end

endmodule