
module bitwise_operation(
    input [7:0] a_in,
    input [7:0] b_in,
    output reg [7:0] out
);

    always @(*) begin
        out[7:2] = a_in[7:2];
        out[1] = ~(a_in[1] ^ b_in[1]);
        out[0] = a_in[0] ^ b_in[0];
    end

endmodule
