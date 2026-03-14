module top_module(
    input a,
    input b,
    input c,
    input d,
    output reg out_func
);

reg xor1_out, xor2_out;

always @(*) begin
    xor1_out = a ^ b;
end

always @(*) begin
    xor2_out = c ^ d;
end

always @(*) begin
    if (xor1_out == 0 && xor2_out == 0)
        out_func = 0;
    else if (xor1_out == 1 || xor2_out == 1)
        out_func = 1;
    else
        out_func = 0;
end

endmodule