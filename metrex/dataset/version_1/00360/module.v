




module
    sameRecFN#(parameter expWidth = 3, parameter sigWidth = 3) (
        input [(expWidth + sigWidth):0] a,
        input [(expWidth + sigWidth):0] b,
        output out
    );

    wire [3:0] top4A = a[(expWidth + sigWidth):(expWidth + sigWidth - 3)];
    wire [3:0] top4B = b[(expWidth + sigWidth):(expWidth + sigWidth - 3)];
    assign out =
        (top4A[2:0] == 'b000) || (top4A[2:0] == 'b111)
            ? (top4A == top4B) && (a[(sigWidth - 2):0] == b[(sigWidth - 2):0])
            : (top4A[2:0] == 'b110) ? (top4A == top4B) : (a == b);

endmodule

