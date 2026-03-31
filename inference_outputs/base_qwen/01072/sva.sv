```systemverilog
module four_bit_adder_sva(
    input logic CLK,
    input logic RESETn,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    output logic [3:0] S,
    output logic C_out
);

    // Full adder logic is combinational, so we use @(posedge CLK) for assertions.

    // Cin can only transition from HIGH to LOW when all outputs are LOW.
    cin_transition: assert property (
        @(posedge CLK) disable iff (!RESETn) $fell(Cin) |-> (S == 4'b0000) && (C_out == 1'b0)
    );

    // S[0] can only transition from HIGH to LOW when A[0] and B[0] are both LOW and Cin is LOW.
    s0_transition: assert property (
        @(posedge CLK) disable iff (!RESETn) $fell(S[0]) |-> (A[0] == 1'b0) && (B[0] == 1'b0) && (Cin == 1'b0)
    );

    // S[1] can only transition from HIGH to LOW when A[1] and B[1] are both LOW and C_out is LOW.
    s1_transition: assert property (
        @(posedge CLK) disable iff (!RESETn) $fell(S[1]) |-> (A[1] == 1'b0) && (B[1] == 1'b0) && (C_out == 1'b0)
    );

    // S[2] can only transition from HIGH to LOW when A[2] and B[2] are both LOW and C_out is LOW.
    s2_transition: assert property (
        @(posedge CLK) disable iff (!RESETn) $fell(S[2]) |-> (A[2] == 1'b0) && (B[2] == 1'b0) && (C_out == 1'b0)
    );

    // S[3] can only transition from HIGH to LOW when A[3] and B[3] are both LOW and C_out is LOW.
    s3_transition: assert property (
        @(posedge CLK) disable iff (!RESETn) $fell(S[3]) |-> (A[3] == 1'b0) && (B[3] == 1'b0) && (C_out == 1'b0)
    );

    // C_out can only transition from HIGH to LOW when all outputs are LOW.
    cout_transition: assert property (
        @(posedge CLK) disable iff (!RESETn) $fell(C_out) |-> (S == 4'b0000)
    );

    // At reset assertion, all outputs must drive LOW.
    reset: assert property (
        @(posedge CLK) !RESETn |-> (S == 4'b0000) && (C_out == 1'b0)
    );

endmodule
```