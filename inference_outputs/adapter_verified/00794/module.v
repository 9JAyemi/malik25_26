module split_16bit_input(
    input wire clk,
    input wire [15:0] in,
    output reg [7:0] out_hi,
    output reg [7:0] out_lo
);

always @(posedge clk) begin
    out_hi <= in[15:8];
    out_lo <= in[7:0];
end

endmodule

module top_module( 
    input wire clk,
    input wire [15:0] in,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo );

split_16bit_input split_input(
    .clk(clk),
    .in(in),
    .out_hi(out_hi),
    .out_lo(out_lo)
);

endmodule