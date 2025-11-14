module and3 (
    input a,
    input b,
    input c,
    output y
);

    wire and1_out;
    wire and2_out;
    wire and3_out;

    and2 and1(.a(a), .b(b), .y(and1_out));
    and2 and2(.a(and1_out), .b(c), .y(and2_out));
    and2 and3(.a(and2_out), .b(and1_out), .y(y));

endmodule

module and2(a, b, y);
input a, b;
output y;

assign y = a&b;

endmodule