
module top_module (
    input [3:0] in0,
    input [3:0] in1,
    input DIR,
    input [1:0] AMT,
    output wire eq,
    output wire gt,
    output wire lt,
    output wire [3:0] out
);

wire [3:0] shifted_in0;

// Barrel shifter
barrel_shifter bs (
    .in(in0),
    .shift_dir(DIR),
    .shift_amt(AMT),
    .out(shifted_in0)
);

// Comparator
comparator cmp (
    .in1(shifted_in0),
    .in2(in1),
    .eq(eq),
    .gt(gt),
    .lt(lt)
);

// Output
assign out = shifted_in0;

endmodule

module barrel_shifter (
    input [3:0] in,
    input shift_dir,
    input [1:0] shift_amt,
    output [3:0] out
);

assign out = shift_dir ? in >> shift_amt : in << shift_amt;

endmodule

module comparator (
    input [3:0] in1,
    input [3:0] in2,
    output eq,
    output gt,
    output lt
);

assign eq = (in1 == in2);
assign gt = (in1 > in2);
assign lt = (in1 < in2);

endmodule
