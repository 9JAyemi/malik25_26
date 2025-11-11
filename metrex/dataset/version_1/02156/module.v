module and_module(
    input wire a,
    input wire b,
    input wire c,
    input wire d,
    output wire out0,
    output wire out1,
    output wire out2,
    output wire out3
);

    assign out0 = a & b;
    assign out1 = b & c;
    assign out2 = (a == 1) ? d : 1'b0;
    assign out3 = b & d;

endmodule

