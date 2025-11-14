
module ram_control(
    input clk,
    input enable,
    input [11:0] addrA,
    input [11:0] addrB,
    input [11:0] addrW,
    input [8:0] dataIn,
    output reg [8:0] dataOutA,
    output reg [8:0] dataOutB
);

reg [8:0] dataOutA_reg;
reg [8:0] dataOutB_reg;

reg [8:0] ram [4095:0];

always @(posedge clk) begin
    if (enable) begin
        dataOutA <= ram[addrA];
        dataOutB <= ram[addrB];
        ram[addrW] <= dataIn;
    end
end

endmodule