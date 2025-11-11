
module SP_RAM_32x512(
    input clk,
    input rce,
    input [8:0] ra,
    output reg [31:0] rq,
    input wce,
    input [8:0] wa,
    input [31:0] wd
);

parameter AWIDTH = 9;
parameter DWIDTH = 32;

reg [DWIDTH-1:0] bram_out;
wire [DWIDTH-1:0] bram_in;

assign bram_in = wce ? wd : {DWIDTH{1'b0}};

BRAM_SDP_32x512 #(.AWIDTH(AWIDTH), .DWIDTH(DWIDTH))
BRAM_32x512 (.clk(clk),
                     .rce(rce),
                     .ra(ra),
                     .rq(bram_out),
                     .wce(wce),
                     .wa(wa),
                     .wd(bram_in));

always @(posedge clk) begin
    if (rce) begin
        rq <= bram_out;
    end
end

endmodule
module BRAM_SDP_32x512 (
    input clk,
    input rce,
    input [8:0] ra,
    output reg [31:0] rq,
    input wce,
    input [8:0] wa,
    input [31:0] wd
);

parameter AWIDTH = 9;
parameter DWIDTH = 32;

reg [DWIDTH-1:0] memory [0:511];

always @(posedge clk) begin
    if (wce) begin
        memory[wa] <= wd;
    end
    if (rce) begin
        rq <= memory[ra];
    end
end

endmodule