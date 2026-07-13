module ripple_carry_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CIN,
    input logic [3:0] SUM,
    input logic COUT
);

// SUM[0] matches the full-adder XOR equation.
    check_sum_bit0: assert property (
        @(posedge clk) SUM[0] == (A[0] ^ B[0] ^ CIN)
    );

// SUM[1] uses the carry generated from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) SUM[1] == (A[1] ^ B[1] ^ ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0])))
    );

// SUM[2] uses the carry generated from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk) SUM[2] == (A[2] ^ B[2] ^ ((A[1] & B[1]) | (B[1] & ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0]))) | ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0])) & A[1])))
    );

// SUM[3] uses the carry generated from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk) SUM[3] == (A[3] ^ B[3] ^ ((A[2] & B[2]) | (B[2] & ((A[1] & B[1]) | (B[1] & ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0]))) | ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0])) & A[1]))) | ((A[1] & B[1]) | (B[1] & ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0]))) | ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0])) & A[1])) & A[2])))
    );

// COUT matches the carry-out equation from the final full adder.
    check_cout: assert property (
        @(posedge clk) COUT == ((A[3] & B[3]) | (B[3] & ((A[2] & B[2]) | (B[2] & ((A[1] & B[1]) | (B[1] & ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0]))) | ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0])) & A[1]))) | ((A[1] & B[1]) | (B[1] & ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0]))) | ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0])) & A[1])) & A[2]))) | ((A[2] & B[2]) | (B[2] & ((A[1] & B[1]) | (B[1] & ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0]))) | ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0])) & A[1]))) | ((A[1] & B[1]) | (B[1] & ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0]))) | ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0])) & A[1])) & A[2])) & ((A[1] & B[1]) | (B[1] & ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0]))) | ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0])) & A[1])) & ((A[0] & B[0]) | (B[0] & CIN) | (CIN & A[0])))
    );

endmodule
