```systemverilog
module ripple_carry_adder_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic CI,
    output logic [3:0] S,
    output logic CO
);

    // Combinational logic: S and CO are determined by A, B, and CI
    // Clocked assertions to ensure correct behavior at each clock edge

    // S[0] is determined by A[0], B[0], and CI
    comb_s0: assert property (
        @(posedge CLK) disable iff (!RESETn) S[0] == A[0] ^ B[0] ^ CI
    );

    // S[1] is determined by A[1], B[1], and C[0]
    comb_s1: assert property (
        @(posedge CLK) disable iff (!RESETn) S[1] == A[1] ^ B[1] ^ C[0]
    );

    // S[2] is determined by A[2], B[2], and C[1]
    comb_s2: assert property (
        @(posedge CLK) disable iff (!RESETn) S[2] == A[2] ^ B[2] ^ C[1]
    );

    // S[3] is determined by A[3], B[3], and C[2]
    comb_s3: assert property (
        @(posedge CLK) disable iff (!RESETn) S[3] == A[3] ^ B[3] ^ C[2]
    );

    // CO is determined by C[2]
    comb_co: assert property (
        @(posedge CLK) disable iff (!RESETn) CO == C[2]
    );

    // Internal carry signals C[0], C[1], C[2] are determined by their respective adders
    // C[0] is determined by A[0], B[0], and CI
    comb_c0: assert property (
        @(posedge CLK) disable iff (!RESETn) C[0] == A[0] & B[0] | B[0] & CI | A[0] & CI
    );

    // C[1] is determined by A[1], B[1], and C[0]
    comb_c1: assert property (
        @(posedge CLK) disable iff (!RESETn) C[1] == A[1] & B[1] | B[1] & C[0] | A[1] & C[0]
    );

    // C[2] is determined by A[2], B[2], and C[1]
    comb_c2: assert property (
        @(posedge CLK) disable iff (!RESETn) C[2] == A[2] & B[2] | B[2] & C[1] | A[2] & C[1]
    );

endmodule
```