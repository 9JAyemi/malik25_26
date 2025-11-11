module calculator(
    input clk,
    input rst,
    input [1:0] op,
    input [31:0] a,
    input [31:0] b,
    output reg [31:0] result
);

always @ (posedge clk) begin
    if (rst == 1) begin
        result <= 0;
    end
    else begin
        case (op)
            2'b00: result <= a + b;
            2'b01: result <= a - b;
            2'b10: result <= a * b;
            2'b11: result <= a / b;
        endcase
    end
end

endmodule