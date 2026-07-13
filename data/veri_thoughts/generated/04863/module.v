module reverse_byte_order(
    input [7:0] in,
    output [7:0] out
);
    assign out = {in[7:4], in[3:0]};
endmodule

module dff_8(
    input clk,
    input [7:0] d,
    input reset,
    output reg [7:0] q
);
    always @(negedge clk) begin
        if (reset) begin
            q <= 8'h00;
        end else begin
            q <= d;
        end
    end
endmodule

module adder_module (
    input clk,
    input reset, // Synchronous active-high reset
    input [31:0] in1, // 32-bit input for first 8-bit value
    input [31:0] in2, // 32-bit input for second 8-bit value
    output [7:0] q // 8-bit output for the sum
);
    wire [7:0] rev_in1, rev_in2;
    wire [7:0] sum;
    reverse_byte_order rbo1(.in(in1[7:0]), .out(rev_in1));
    reverse_byte_order rbo2(.in(in2[7:0]), .out(rev_in2));
    assign sum = rev_in1 + rev_in2;
    dff_8 dff_inst(.clk(clk), .d(sum), .reset(reset), .q(q));
endmodule