module shift_register (
    input clk,
    input [3:0] D,
    input SI,
    output reg SO
);

reg [3:0] reg1, reg2, reg3, reg4;

always @(posedge clk) begin
    reg4 <= reg3;
    reg3 <= reg2;
    reg2 <= reg1;
    reg1 <= SI ? D : reg1;
    SO <= reg4[0];
end

endmodule