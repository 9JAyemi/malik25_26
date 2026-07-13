
module top_module(
    input wire clk,
    input wire [7:0] in1,
    input wire [7:0] in2,
    input wire sel,
    output wire [7:0] sum
);

    wire [7:0] add_out;
    wire carry_out;
    wire [7:0] mux_out;

    genvar i;
    generate
        for (i=0; i<8; i=i+1) begin: adder_loop
            full_adder adder_inst(
                .a(in1[i]),
                .b(in2[i]),
                .cin(sel),
                .sum(add_out[i]),
                .cout() // Disconnect carry out
            );

            mux2to1 mux_inst(
                .a(in1[i]),
                .b(in2[i]),
                .sel(sel),
                .out(mux_out[i])
            );
        end
    endgenerate

    assign sum = sel ? mux_out : add_out;

endmodule
module full_adder(
    input wire a,
    input wire b,
    input wire cin,
    output wire sum,
    output wire cout
);

    assign {cout, sum} = a + b + cin;

endmodule
module mux2to1(
    input wire  a,
    input wire  b,
    input wire sel,
    output wire  out
);

    assign out = sel ? b : a;

endmodule