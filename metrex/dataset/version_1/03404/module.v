module voltage_supply (
  input clk,
  input rst,
  input enable,
  output reg VPWR,
  output reg VGND,
  output reg VPB,
  output reg VNB
);

  always @(posedge clk or posedge rst) begin
    if (rst) begin
      VPB <= 0;
      VNB <= 0;
    end else if (enable) begin
      VPB <= #2 ~VPB;
      VNB <= 0;
    end else begin
      VPB <= 0;
      VNB <= 0;
    end
  end

  initial begin
    VPWR = 1;
    VGND = 0;
  end

endmodule