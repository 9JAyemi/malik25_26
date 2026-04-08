module RegisterAdd_1 (
    input clk,
    input rst,
    input load,
    input [0:0] D,
    output [0:0] Q
);

    reg [0:0] Q_next;
    reg [0:0] Q_reg;
    reg [0:0] D_reg;

    assign Q = Q_reg;

    always @ (posedge clk or posedge rst) begin
        if (rst) begin
            Q_reg <= 1'b0;
        end else begin
            Q_reg <= Q_next;
        end
    end

    always @ (*) begin
        D_reg[0] = D[0];
        Q_next[0] = (load == 1'b1) ? D[0] : (Q_reg[0] + D_reg[0]);
    end

endmodule