
module srlc32e(
    input [31:0] D,
    input CLK,
    input CE,
    input A,
    output Q
);

    reg [31:0] Q_reg;

    always @(posedge CLK) begin
        if (CE) begin
            Q_reg <= D;
        end
    end

    assign Q = Q_reg[A];

endmodule