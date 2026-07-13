
module RegisterAdder
   (D,
    Q_reg_0,
    Q,
    Q_reg_2,
    CLK,
    AR);
  output [1:0] D;
  output [0:0] Q_reg_0;
  input [1:0] Q;
  input [1:0] Q_reg_2;
  input CLK;
  input AR;

  wire [1:0] D;
  wire [0:0] Q_reg_0;
  reg [1:0] Q_reg_temp; // Changed wire to reg

  assign D = Q + Q_reg_2;

  always @(posedge CLK, negedge AR) begin
    if (!AR) begin
      Q_reg_temp <= 2'b0;
    end else begin
      Q_reg_temp <= D; // Corrected the assignment
    end
  end

  assign Q_reg_0 = Q_reg_temp[0];

endmodule
