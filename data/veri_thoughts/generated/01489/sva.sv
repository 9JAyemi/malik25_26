module bitwise_and_4bit_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] M
);
    // No clock/reset present; pure combinational: M = A & B

    // Output equals bitwise AND of inputs at all times.
    always_comb begin
        check_and_function: assert (M == (A & B));
    end
endmodule