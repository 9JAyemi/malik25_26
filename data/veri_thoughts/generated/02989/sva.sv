module adder_4bit_sva (
    input logic CLK,        // sampling clock for assertions (DUT has no clock)
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S,
    input logic C
);
    // Clock: external CLK (no reset in DUT). Logic: purely combinational. Behavior: S=A+B (4-bit), C=S[3].

    // S equals 4-bit sum of A and B.
    check_sum_is_add: assert property (
        @(posedge CLK) S === (A + B)
    );

    // C mirrors the MSB of S.
    check_c_eq_s_msb: assert property (
        @(posedge CLK) C === S[3]
    );

    // C equals the MSB of the 4-bit sum (consistent with S assignment).
    check_c_eq_add_msb: assert property (
        @(posedge CLK) C === (A + B)[3]
    );

    // Adding zero on B leaves S equal to A.
    check_identity_b_zero: assert property (
        @(posedge CLK) (B === 4'b0000) |-> (S === A)
    );

    // Adding zero on A leaves S equal to B.
    check_identity_a_zero: assert property (
        @(posedge CLK) (A === 4'b0000) |-> (S === B)
    );

    // If A and B are unchanged from last cycle, S and C are unchanged.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge CLK) ((A === $past(A)) && (B === $past(B))) |-> ((S === $past(S)) && (C === $past(C)))
    );

endmodule