module excess_3_converter (
    input [3:0] binary,
    output [7:0] excess_3
);

assign excess_3 = {4'b0000, binary + 4'b0011};

endmodule
