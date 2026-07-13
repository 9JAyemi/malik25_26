module three_bit_splitter (
    input wire [2:0] in_vec,
    output wire o0,
    output wire o1,
    output wire o2
);
    assign o0 = in_vec[0];
    assign o1 = in_vec[1];
    assign o2 = in_vec[2];
endmodule

module barrel_shifter (
    input wire [15:0] in,
    output wire [7:0] upper,
    output wire [7:0] lower
);
    assign upper = in[15:8];
    assign lower = in[7:0];
endmodule

module adder_8bit (
    input wire [7:0] a,
    input wire [7:0] b,
    output wire [7:0] sum
);
    assign sum = a + b;
endmodule

module top_module (
    input wire [15:0] in,
    output wire [7:0] out_sum
);
    wire [7:0] upper;
    wire [7:0] lower;

    barrel_shifter bs (
        .in(in),
        .upper(upper),
        .lower(lower)
    );

    adder_8bit add (
        .a(upper),
        .b(lower),
        .sum(out_sum)
    );
endmodule