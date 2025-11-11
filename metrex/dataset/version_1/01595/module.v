module conflict_ff_clk (
    input wire CLK1,
    input wire CLK2,
    input wire [8:0] A,
    input wire [8:0] B,
    output reg [17:0] Z
);

    always @(posedge CLK2)
        Z <= {B[8:0], Z[17:9]};

endmodule

module MULT9X9 (
    input wire [8:0] A,
    input wire [8:0] B,
    output reg [17:0] Z
);

    always @*
        Z = A * B;

endmodule