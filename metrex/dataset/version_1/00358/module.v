
module magnitude_comparator (
    input [3:0] in_1,
    input [3:0] in_0,
    output greater_than_or_equal
);

    assign greater_than_or_equal = (in_1 == in_0) ? 1'b1 :
                                   (in_1[3] != in_0[3]) ? (in_1[3] == 1'b0) :
                                   (in_1 > in_0);

endmodule
