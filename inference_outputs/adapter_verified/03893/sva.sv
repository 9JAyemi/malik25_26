module ripple_carry_adder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] SUM
);

// SUM[0] matches the first full-adder XOR equation.
    check_sum_bit0: assert property (
        @(posedge CLK) SUM[0] == (A[0] ^ B[0] ^ 1'b0)
    );

// SUM[1] uses the carry generated from bit 0.
    check_sum_bit1: assert property (
        @(posedge CLK) SUM[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (1'b0 & (A[0] ^ B[0]))))
    );

// SUM[2] uses the carry generated from bit 1.
    check_sum_bit2: assert property (
        @(posedge CLK) SUM[2] == (A[2] ^ B[2] ^ ((A[1] & B[1]) | ((A[0] & B[0]) | (1'b0 & (A[0] ^ B[0])))))
    );

// SUM[3] uses the carry generated from bit 2.
    check_sum_bit3: assert property (
        @(posedge CLK) SUM[3] == (A[3] ^ B[3] ^ ((A[2] & B[2]) | ((A[1] & B[1]) | ((A[0] & B[0]) | (1'b0 & (A[0] ^ B[0]))))))
    );

endmodule
