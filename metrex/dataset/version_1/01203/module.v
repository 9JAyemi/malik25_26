
module d_ff(
    input clk,
    input d,
    output reg q
);
    always @(posedge clk) begin
        q <= d;
    end
endmodule
module xor_gate(
    input [2:0] a,
    input [2:0] b,
    output [2:0] out_xor
);
    assign out_xor = a ^ b;
endmodule
module and_gate(
    input [2:0] a,
    input [2:0] b,
    output [2:0] out_and
);
    assign out_and = a & b;
endmodule
module top_module( 
    input [2:0] a,
    input [2:0] b,
    input select,
    input clk,
    output reg [2:0] out_xor_bitwise,
    output reg out_and_logical,
    output reg [5:0] out_not
);
    wire [2:0] xor_out;
    wire [2:0] and_out;
    wire [2:0] a_not;
    wire [2:0] b_not;

    xor_gate xor_inst(.a(a), .b(b), .out_xor(xor_out));
    and_gate and_inst(.a(a), .b(b), .out_and(and_out));
    d_ff d_ff_inst_a(.clk(clk), .d(~a[0]), .q(a_not[0]));
    d_ff d_ff_inst_b(.clk(clk), .d(~b[0]), .q(b_not[0]));
    d_ff d_ff_inst_a_1(.clk(clk), .d(~a[1]), .q(a_not[1]));
    d_ff d_ff_inst_b_1(.clk(clk), .d(~b[1]), .q(b_not[1]));
    d_ff d_ff_inst_a_2(.clk(clk), .d(~a[2]), .q(a_not[2]));
    d_ff d_ff_inst_b_2(.clk(clk), .d(~b[2]), .q(b_not[2]));

    always @(*) begin
        if (select == 1'b1) begin
            out_xor_bitwise <= xor_out;
            out_and_logical <= and_out[0];
            out_not[2:0] <= b_not;
            out_not[5:3] <= a_not;
        end
        else begin
            out_xor_bitwise <= 3'b0;
            out_and_logical <= 1'b0;
            out_not <= {~a, ~b, 3'b0, 3'b0};
        end
    end
endmodule