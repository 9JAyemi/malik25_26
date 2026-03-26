
module alu_16(
    input clk,
    input [15:0] a,
    input [15:0] b,
    input [7:0] ctrl,
    output reg [15:0] out,
    output reg n,
    output reg z,
    output reg c,
    output reg v
);

wire [15:0] add_out;
wire [15:0] sub_out;
wire [15:0] slt_out;
wire [15:0] sll_out;
wire [15:0] srl_out;
wire [15:0] sra_out;
wire [15:0] and_out;
wire [15:0] or_out;

// AND operation
assign and_out = a & b;
// OR operation
assign or_out = a | b;
// ADD operation
assign add_out = a + b;
// SUB operation
assign sub_out = a - b;
// SLT operation
assign slt_out = (a < b) ? 16'h0001 : 16'h0000;
// SLL operation
assign sll_out = a << b[3:0];
// SRL operation
assign srl_out = a >> b[3:0];
// SRA operation
assign sra_out = ($signed(a) >>> b[3:0]);

// Output selection based on control input
always @* begin
    case(ctrl)
        8'b000_0000: out = and_out;
        8'b000_0001: out = or_out;
        8'b000_0010: out = add_out;
        8'b000_0011: out = sub_out;
        8'b000_0100: out = slt_out;
        8'b000_0101: out = sll_out;
        8'b000_0110: out = srl_out;
        8'b000_0111: out = sra_out;
        default: out = 16'h0000;
    endcase
end

// Status flag generation
always @* begin
    n = (out[15] == 1) ? 1 : 0;
    z = (out == 16'h0000) ? 1 : 0;
    c = (out[15] == 1) ? 1 : 0;
    v = (((a[15] == 0) && (b[15] == 0) && (out[15] == 1)) || ((a[15] == 1) && (b[15] == 1) && (out[15] == 0))) ? 1 : 0;
end

endmodule