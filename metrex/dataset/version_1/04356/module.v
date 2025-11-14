
module top(
    input  wire [3:0] di,
    output wire       do
);

    wire [3:0] d;

    not n0 (d[0], di[0]);
    not n1 (d[1], di[1]);
    not n2 (d[2], di[2]);
    not n3 (d[3], di[3]);

    assign do = ~((d[1] & d[0]) | (d[3] & d[2]));

endmodule
