module four_bit_adder_sva (
    input logic CLK,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic Cin,
    input logic [3:0] S
);
    // S equals add/sub based on Cin (mod 16).
    check_function_select: assert property (
        @(posedge CLK) S == (Cin ? (A - B) : (A + B))[3:0]
    );

    // When Cin=0, S == A+B (mod 16).
    check_sum_when_cin0: assert property (
        @(posedge CLK) (Cin == 1'b0) |-> (S == (A + B)[3:0])
    );

    // When Cin=1, S == A-B (mod 16).
    check_diff_when_cin1: assert property (
        @(posedge CLK) (Cin == 1'b1) |-> (S == (A - B)[3:0])
    );

    // If inputs stable across a cycle, output remains stable.
    check_stability_no_input_change: assert property (
        @(posedge CLK) ($stable(A) && $stable(B) && $stable(Cin)) |-> $stable(S)
    );

    // If Cin rises with A,B stable, S == A-B (mod 16).
    check_cin_rise_selects_sub: assert property (
        @(posedge CLK) ($rose(Cin) && $stable(A) && $stable(B)) |-> (S == (A - B)[3:0])
    );

    // If Cin falls with A,B stable, S == A+B (mod 16).
    check_cin_fall_selects_add: assert property (
        @(posedge CLK) ($fell(Cin) && $stable(A) && $stable(B)) |-> (S == (A + B)[3:0])
    );

    // For Cin=0, A equals S-B (mod 16).
    check_inverse_when_add: assert property (
        @(posedge CLK) (Cin == 1'b0) |-> ((S - B)[3:0] == A)
    );

    // For Cin=1, A equals S+B (mod 16).
    check_inverse_when_sub: assert property (
        @(posedge CLK) (Cin == 1'b1) |-> ((S + B)[3:0] == A)
    );
endmodule