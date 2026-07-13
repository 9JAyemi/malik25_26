
module shift_reg(CK, D, S, Q);
input CK, S;
input [3:0] D;
output [3:0] Q;

wire [3:0] Q_temp;
reg [3:0] Q_reg;

always @ (posedge CK) begin
    if(S) begin
        Q_reg <= D;
    end else begin
        Q_reg <= {Q_reg[2:0], Q_temp[3]};
    end
end

assign Q_temp = Q_reg;
assign Q = Q_reg;

endmodule