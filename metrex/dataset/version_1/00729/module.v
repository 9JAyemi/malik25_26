module pulse
  #(parameter dly=3,
    parameter len=2)
  (input rstn,
   input clk,
   output reg pulse);

  localparam width = $clog2(dly+len)+1;

  reg [width-1:0] cnt;

  always @(posedge clk or negedge rstn) begin
    if (~rstn)
      cnt <= 1'b0;
    else if (cnt != dly+len)
      cnt <= cnt + 1'b1;
  end

  always @(posedge clk or negedge rstn) begin
    if (~rstn)
      pulse <= 1'b0;
    else if (cnt == dly)
      pulse <= 1'b1;
    else if (cnt == dly+len)
      pulse <= 1'b0;
  end
endmodule