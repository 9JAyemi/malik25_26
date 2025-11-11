module ram16k_dualport(
    input CLK,
    input [9:0] A1ADDR, B1ADDR,
    input [31:0] B1DATA,
    input A1EN, B1EN,
    output reg [31:0] A1DATA
);

     reg [31:0] mem [0:4095];

    always @(posedge CLK) begin
        if (B1EN) begin
            mem[B1ADDR] <= B1DATA;
        end
        if (A1EN) begin
            A1DATA <= mem[A1ADDR];
        end
    end

endmodule