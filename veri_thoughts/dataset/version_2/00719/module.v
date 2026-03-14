module two_bit_encoder(
    input [1:0] data,
    output reg q,
    output reg zero
);

always @(*) begin
    q = ~data[0];
    zero = ~(data[0] | data[1]);
end

endmodule