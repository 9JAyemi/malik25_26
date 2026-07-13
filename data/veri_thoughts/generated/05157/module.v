module RegisterAdd_3
  (
    input clk,
    input rst,
    input load,
    input [0:0] D,
    output reg [0:0] Q
  );

  wire [0:0] Q_int;
  wire Q_int_n_0 ;
  
  assign Q_int = Q;

  assign Q_int_n_0 = load & Q;

  always @(posedge clk or posedge rst) begin
    if (rst) begin
      Q <= 1'b0;
    end else if (load) begin
      Q <= D;
    end
  end

endmodule