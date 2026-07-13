
module clk32to40 (
  input CLK_IN1,
  output reg CLK_OUT
);

  // Clock to Q delay of 100ps
  localparam  TCQ              = 100;

  reg [1:0] counter;
  wire reset ;

  always @(posedge CLK_IN1 or negedge reset) begin
    if (!reset) begin
      counter <= 2'b00;
    end else if (counter == 2'b11) begin
      counter <= 2'b00;
    end else begin
      counter <= counter + 1;
    end
  end

  assign reset = (counter == 2'b11);

  always @(posedge CLK_IN1) begin
    if (!reset) CLK_OUT <= 1'b0;
    else begin
      if (counter == 2'b01) CLK_OUT <= 1'b1;
      else if (counter == 2'b10) CLK_OUT <= 1'b0;
    end
  end

endmodule