module adder_subtractor_sva (
    input logic CLK,
    input logic RESETn,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic mode,
    input logic [3:0] result
);
    // In add mode, result equals A+B (4-bit modulo).
    function_add_if_mode0: assert property (
        @(posedge CLK) disable iff (!RESETn) (mode == 1'b0) |-> (result == (A + B))
    );
    // In subtract mode, result equals A-B (4-bit modulo).
    function_sub_if_mode1: assert property (
        @(posedge CLK) disable iff (!RESETn) (mode == 1'b1) |-> (result == (A - B))
    );
    // B==0 leaves result equal to A for both modes.
    identity_B_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (B == 4'h0) |-> (result == A)
    );
    // In add mode with A==0, result equals B.
    add_identity_A_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (mode == 1'b0 && A == 4'h0) |-> (result == B)
    );
    // In subtract mode with A==B, result is zero.
    sub_zero_when_equal: assert property (
        @(posedge CLK) disable iff (!RESETn) (mode == 1'b1 && (A == B)) |-> (result == 4'h0)
    );
    // In add mode with B==0xF, result is A-1 (mod 16).
    add_B_F_decrement: assert property (
        @(posedge CLK) disable iff (!RESETn) (mode == 1'b0 && B == 4'hF) |-> (result == (A - 4'h1))
    );
    // In add mode, (result - B) equals A (mod 16).
    add_inverse_mod_check: assert property (
        @(posedge CLK) disable iff (!RESETn) (mode == 1'b0) |-> ((result - B) == A)
    );
    // In subtract mode, (result + B) equals A (mod 16).
    sub_inverse_mod_check: assert property (
        @(posedge CLK) disable iff (!RESETn) (mode == 1'b1) |-> ((result + B) == A)
    );
    // In subtract mode, result equals A + (~B + 1) (two's complement).
    twos_complement_equivalence_sub: assert property (
        @(posedge CLK) disable iff (!RESETn) (mode == 1'b1) |-> (result == (A + (~B + 4'b0001)))
    );
    // If A,B,mode stable, result remains stable at next sample.
    stability_when_inputs_stable: assert property (
        @(posedge CLK) disable iff (!RESETn) ($stable(A) && $stable(B) && $stable(mode)) |-> $stable(result)
    );
endmodule