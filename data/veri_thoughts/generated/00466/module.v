
module n0(
    input  wire       A,
    output wire       Y
);

    assign Y = ~A;

endmodule
module n1(
    input  wire       A,
    output wire       Y
);

    assign Y = ~A;

endmodule
module box(
    input  wire       A,
    output wire       Y
);

    assign Y = A;

endmodule
module c(
    input  wire       I,
    output wire [1:0] O
);

    assign O = {~I, I};

endmodule
module top(
    input  wire       di,
    output wire [3:0] do
);

    wire [1:0] d;

    n0    n0_inst (.A(di), .Y(d[0]));
    n1    n1_inst (.A(di), .Y(d[1]));
    box   b0_inst (.A(d[0]), .Y(do[0]));
    box   b1_inst (.A(d[1]), .Y(do[1]));
    c     c_inst  (.I(d[1]), .O(do[3:2]));

endmodule