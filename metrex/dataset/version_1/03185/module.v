module register_addition (
  input CLK,
  input AR,
  input [1:0] Q_reg_0,
  input [29:0] Q_reg_30,
  output reg [7:0] Q
);

  reg [7:0] reg_bank [0:7];
  integer i;
  
  always @(posedge CLK or posedge AR) begin
    if (AR) begin
      for (i = 0; i < 8; i = i + 1) begin
        reg_bank[i] <= 8'b0;
      end
    end else begin
      case (Q_reg_0)
        2'b00: reg_bank[0] <= reg_bank[0] + Q_reg_30;
        2'b01: reg_bank[1] <= reg_bank[1] + Q_reg_30;
        2'b10: reg_bank[2] <= reg_bank[2] + Q_reg_30;
        2'b11: reg_bank[3] <= reg_bank[3] + Q_reg_30;
      endcase
      Q <= reg_bank[Q_reg_0];
    end
  end
  
endmodule