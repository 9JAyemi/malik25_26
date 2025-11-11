module select_bits #(
    parameter WIDTH = 16
)(
    input signed [WIDTH-1:0] in,
    output reg [9:0] out
);

    always @(*) begin
        if (in[0] == 1'b0) // even
            out = in[9:0];
        else // odd
            out = in[WIDTH-1:WIDTH-10];
    end

endmodule