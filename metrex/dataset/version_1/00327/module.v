module binary_to_gray (
    input  [7:0] binary_in,
    output [7:0] gray_out
);
    assign gray_out = binary_in ^ ({1'b0, binary_in[7:1]});
endmodule