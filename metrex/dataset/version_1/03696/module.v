`define N 32 
`define K 32
module regfile (
    input clk,
    input ld,
    input [`K-1:0] d,
    input [`N-1:0] sa,
    input [`N-1:0] sb,
    output reg [`N-1:0] a,
    output reg [`N-1:0] b,
    output reg [`K-1:0] x
);

reg [`K-1:0] regfile [`N-1:0];

always @(posedge clk) begin
    if (ld) begin
        regfile[d] <= d;
        x <= regfile[sa];
    end
    a <= regfile[sa];
    b <= regfile[sb];
end

endmodule