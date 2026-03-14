module binary_adder_sva (
    input  logic        CLK,
    input  logic [3:0]  A,
    input  logic [3:0]  B,
    input  logic        C,
    input  logic [3:0]  Z
);
    // Local model mirroring RTL computations
    logic [3:0] A_comp, B_comp;
    logic [4:0] sum5;
    logic [3:0] sum_low;
    logic [3:0] z_expected_c0;
    logic [3:0] z_expected_c1;

    assign A_comp       = (~A) + 4'd1;
    assign B_comp       = (~B) + 4'd1;
    assign sum5         = {1'b0, A_comp} + {1'b0, B_comp} + {4'd0, C};
    assign sum_low      = sum5[3:0];
    assign z_expected_c0 = sum_low;
    assign z_expected_c1 = (~sum_low) + 4'd1;

    // When C=0, Z equals sum_low.
    check_z_when_c0: assert property (
        @(posedge CLK) (C == 1'b0) |-> (Z == z_expected_c0)
    );

    // When C=1, Z equals two's complement of sum_low.
    check_z_when_c1: assert property (
        @(posedge CLK) (C == 1'b1) |-> (Z == z_expected_c1)
    );

    // If A,B stable and C rises, Z becomes bitwise complement of previous Z.
    check_z_complement_on_c_rise: assert property (
        @(posedge CLK) ($stable(A) && $stable(B) && ($past(C,1,C) == 1'b0) && (C == 1'b1)) |-> (Z == ~ $past(Z,1,Z))
    );

    // If A,B stable and C falls, Z becomes bitwise complement of previous Z.
    check_z_complement_on_c_fall: assert property (
        @(posedge CLK) ($stable(A) && $stable(B) && ($past(C,1,C) == 1'b1) && (C == 1'b0)) |-> (Z == ~ $past(Z,1,Z))
    );

    // If A,B,C are all stable, Z must be stable (purely combinational behavior).
    check_output_stable_when_inputs_stable: assert property (
        @(posedge CLK) ($stable(A) && $stable(B) && $stable(C)) |-> $stable(Z)
    );

    // With C=1 and B stable, if A increments by 1 (mod 16), Z increments by 1 (mod 16).
    check_deltaA_inc_when_c1: assert property (
        @(posedge CLK) ($stable(B) && (C == 1'b1) && ($past(C,1,C) == 1'b1) && (A == ($past(A,1,A) + 4'd1))) |-> (Z == ($past(Z,1,Z) + 4'd1))
    );

    // With C=0 and B stable, if A increments by 1 (mod 16), Z decrements by 1 (mod 16).
    check_deltaA_inc_when_c0: assert property (
        @(posedge CLK) ($stable(B) && (C == 1'b0) && ($past(C,1,C) == 1'b0) && (A == ($past(A,1,A) + 4'd1))) |-> (Z == ($past(Z,1,Z) - 4'd1))
    );

    // With C=1 and A stable, if B increments by 1 (mod 16), Z increments by 1 (mod 16).
    check_deltaB_inc_when_c1: assert property (
        @(posedge CLK) ($stable(A) && (C == 1'b1) && ($past(C,1,C) == 1'b1) && (B == ($past(B,1,B) + 4'd1))) |-> (Z == ($past(Z,1,Z) + 4'd1))
    );

    // With C=0 and A stable, if B increments by 1 (mod 16), Z decrements by 1 (mod 16).
    check_deltaB_inc_when_c0: assert property (
        @(posedge CLK) ($stable(A) && (C == 1'b0) && ($past(C,1,C) == 1'b0) && (B == ($past(B,1,B) + 4'd1))) |-> (Z == ($past(Z,1,Z) - 4'd1))
    );

    // Alternative form for C=0: Z equals two's complement of (A+B) modulo 16.
    check_alt_formula_c0: assert property (
        @(posedge CLK) (C == 1'b0) |-> (Z == ((~(({1'b0, A} + {1'b0, B})[3:0])) + 4'd1))
    );

    // Alternative form for C=1: Z equals (A + B - 1) modulo 16.
    check_alt_formula_c1: assert property (
        @(posedge CLK) (C == 1'b1) |-> (Z == (({1'b0, A} + {1'b0, B} + 5'd15)[3:0]))
    );

endmodule