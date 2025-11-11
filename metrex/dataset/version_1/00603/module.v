
module synchronizer_ff #(parameter N = 4)
   (input [N-1:0] D,
    output [N-1:0] Q,
    input s_aclk,
    input rd_rst_reg_reg);

  wire [N-1:0] Q_reg;

     reg [N-1:0] Q_reg_reg;

  
  assign Q = Q_reg_reg;

  always@(posedge s_aclk ) begin
    if(!rd_rst_reg_reg) begin
       Q_reg_reg <= 'b0;
    end
    else begin
       Q_reg_reg <= D;
    end
  end
endmodule