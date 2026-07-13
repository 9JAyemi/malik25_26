
module top_module (
    input clk,
    input [7:0] d,
    input select, // Select input to choose between AND, OR, or XOR
    output out // Output of the selected logic function
);

reg [7:0] q; // Output of the D flip-flops

// D flip-flop module instantiation
d_ff dff0 (.clk(clk), .d(d[0]), .q(q[0]));
d_ff dff1 (.clk(clk), .d(d[1]), .q(q[1]));
d_ff dff2 (.clk(clk), .d(d[2]), .q(q[2]));
d_ff dff3 (.clk(clk), .d(d[3]), .q(q[3]));
d_ff dff4 (.clk(clk), .d(d[4]), .q(q[4]));
d_ff dff5 (.clk(clk), .d(d[5]), .q(q[5]));
d_ff dff6 (.clk(clk), .d(d[6]), .q(q[6]));
d_ff dff7 (.clk(clk), .d(d[7]), .q(q[7]));

// Logic function module instantiation
logic_function logic_func (.in(q), .select(select), .out(out));

endmodule
module d_ff (
    input clk,
    input d,
    output reg q
);
always @(posedge clk) begin // Fixed the clock edge
    q <= d;
end
endmodule
module logic_function (
    input [7:0] in,
    input select,
    output out
);
wire [7:0] and_out;
wire [7:0] or_out;
wire [7:0] xor_out;

assign and_out = &in;
assign or_out = |in;
assign xor_out = ^in;

// Select the output of the desired logic function
assign out = select ? (select == 2'b01 ? or_out : xor_out) : and_out; // Fixed the case statement

endmodule