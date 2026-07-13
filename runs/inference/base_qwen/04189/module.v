module shift_reg (
    input CLK,
    input RST,
    input LD,
    input [3:0] D,
    output [3:0] OUT
);

reg [3:0] reg1, reg2, reg3, reg4;

always @(posedge CLK) begin
    if (RST) begin
        reg1 <= 4'b0;
        reg2 <= 4'b0;
        reg3 <= 4'b0;
        reg4 <= 4'b0;
    end else if (LD) begin
        reg1 <= D;
        reg2 <= reg1;
        reg3 <= reg2;
        reg4 <= reg3;
    end else begin
        reg1 <= reg2;
        reg2 <= reg3;
        reg3 <= reg4;
        reg4 <= reg4;
    end
end

assign OUT = reg4;

endmodule