
module up_down_counter (
    input CLK,
    input RST,
    input LD,
    input UD,
    input [3:0] D,
    output [3:0] Q
);
    
    reg [3:0] Q_reg1, Q_reg2;
    
    always @(posedge CLK) begin
        if(RST) begin
            Q_reg1 <= 4'b0;
            Q_reg2 <= 4'b0;
        end
        else if(LD) begin
            Q_reg1 <= D;
            Q_reg2 <= D;
        end
        else if(UD) begin
            Q_reg1 <= Q_reg2 + 4'b1;
        end
        else begin
            Q_reg1 <= Q_reg2 - 4'b1;
        end
        Q_reg2 <= Q_reg1;
    end
    
    assign Q = Q_reg1;
    
endmodule