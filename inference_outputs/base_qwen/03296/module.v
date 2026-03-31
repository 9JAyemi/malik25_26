
module compare_signed_mag (
    input [3:0] A,
    input [3:0] B,
    output equal,
    output signed_larger,
    output signed_smaller,
    output [3:0] larger_num,
    output [3:0] smaller_num
);

    // Compare the two numbers
    assign equal = (A == B);
    assign signed_larger = ($signed(A) > $signed(B));
    assign signed_smaller = ($signed(A) < $signed(B));
    assign larger_num = (signed_larger) ? A : B;
    assign smaller_num = (signed_smaller) ? A : B;

endmodule

module shift_right (
    input [3:0] in,
    input [1:0] shift_amt,
    input mode,
    output [3:0] out
);

    // Shift the input to the right
    assign out = (mode) ? in >> shift_amt : in >>> shift_amt;

endmodule

module top_module (
    input [3:0] A,
    input [3:0] B,
    input [1:0] shift_amt,
    input mode,
    output reg [3:0] out
);

    // Instantiate the compare_signed_mag module
    wire equal, signed_larger, signed_smaller;
    wire [3:0] larger_num, smaller_num;
    compare_signed_mag cmp (
        .A(A),
        .B(B),
        .equal(equal),
        .signed_larger(signed_larger),
        .signed_smaller(signed_smaller),
        .larger_num(larger_num),
        .smaller_num(smaller_num)
    );

    // Instantiate the shift_right module
    wire [3:0] shifted_num;
    shift_right shift (
        .in(larger_num),
        .shift_amt(shift_amt),
        .mode(mode),
        .out(shifted_num)
    );

    // Assign the output based on the comparison results
    always @(*) begin
        if (equal) begin
            out = 0;
        end else if (signed_larger) begin
            out = shifted_num;
        end else begin
            out = smaller_num;
        end
    end
endmodule
