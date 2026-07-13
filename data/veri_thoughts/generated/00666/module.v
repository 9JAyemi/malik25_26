
module dff_with_reset (
    input clk,
    input reset,
    input [7:0] d,
    output reg [7:0] q
);

always @(negedge clk or posedge reset) begin
    if (reset)
        q <= 0;
    else
        q <= d;
end

endmodule
module half_adder (
    input a,
    input b,
    output sum,
    output carry_out
);

assign sum = a ^ b;
assign carry_out = a & b;

endmodule
module top_module (
    input clk,
    input reset,            // Asynchronous reset
    input [7:0] a,
    input [7:0] b,
    output [7:0] sum,
    output [7:0] carry_out
);

wire [7:0] dff_q;
wire [7:0] half_adder_sum;
wire [7:0] half_adder_carry_out;

dff_with_reset dff_inst (
    .clk(clk),
    .reset(reset),
    .d(a),
    .q(dff_q)
);

half_adder half_adder_inst (
    .a(a[0]),
    .b(b[0]),
    .sum(half_adder_sum[0]),
    .carry_out(half_adder_carry_out[0])
);

half_adder half_adder_inst1 (
    .a(a[1]),
    .b(b[1]),
    .sum(half_adder_sum[1]),
    .carry_out(half_adder_carry_out[1])
);

half_adder half_adder_inst2 (
    .a(a[2]),
    .b(b[2]),
    .sum(half_adder_sum[2]),
    .carry_out(half_adder_carry_out[2])
);

half_adder half_adder_inst3 (
    .a(a[3]),
    .b(b[3]),
    .sum(half_adder_sum[3]),
    .carry_out(half_adder_carry_out[3])
);

half_adder half_adder_inst4 (
    .a(a[4]),
    .b(b[4]),
    .sum(half_adder_sum[4]),
    .carry_out(half_adder_carry_out[4])
);

half_adder half_adder_inst5 (
    .a(a[5]),
    .b(b[5]),
    .sum(half_adder_sum[5]),
    .carry_out(half_adder_carry_out[5])
);

half_adder half_adder_inst6 (
    .a(a[6]),
    .b(b[6]),
    .sum(half_adder_sum[6]),
    .carry_out(half_adder_carry_out[6])
);

half_adder half_adder_inst7 (
    .a(a[7]),
    .b(b[7]),
    .sum(half_adder_sum[7]),
    .carry_out(half_adder_carry_out[7])
);

assign sum = half_adder_sum;
assign carry_out = half_adder_carry_out;

endmodule