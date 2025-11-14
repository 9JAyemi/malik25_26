
module memory(
    input [5:0] a,
    input [31:0] d,
    input clk,
    input we,
    output [31:0] spo
);

wire [31:0] mem_out;

reg [31:0] mem [63:0];

assign spo = mem_out;

always @(posedge clk) begin
    if (we) begin
        mem[a] <= d;
    end
end

assign mem_out = mem[a];

endmodule