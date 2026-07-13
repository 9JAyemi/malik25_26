module binary_adder_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] S
);
    // S equals (A+B) modulo 16.
    check_sum_mod16: assert property (
        @(posedge clk) S == ((A + B) & 4'hF)
    );

    // If inputs hold their values, S holds as well.
    check_stable_if_inputs_hold: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> $stable(S)
    );

    // Adding zero on B leaves S equal to A.
    check_identity_B_zero: assert property (
        @(posedge clk) (B == 4'd0) |-> (S == A)
    );

    // Adding zero on A leaves S equal to B.
    check_identity_A_zero: assert property (
        @(posedge clk) (A == 4'd0) |-> (S == B)
    );

    // Both inputs zero results in zero sum.
    check_zero_plus_zero: assert property (
        @(posedge clk) (A == 4'd0 && B == 4'd0) |-> (S == 4'd0)
    );

    // If A is stable and B increments by 1 (mod 16), S increments by 1 (mod 16).
    check_increment_B: assert property (
        @(posedge clk) ($stable(A) && (B == $past(B) + 4'd1)) |-> (S == $past(S) + 4'd1)
    );

    // If A is stable and B decrements by 1 (mod 16), S decrements by 1 (mod 16).
    check_decrement_B: assert property (
        @(posedge clk) ($stable(A) && (B == $past(B) - 4'd1)) |-> (S == $past(S) - 4'd1)
    );

    // If B is stable and A increments by 1 (mod 16), S increments by 1 (mod 16).
    check_increment_A: assert property (
        @(posedge clk) ($stable(B) && (A == $past(A) + 4'd1)) |-> (S == $past(S) + 4'd1)
    );

    // If B is stable and A decrements by 1 (mod 16), S decrements by 1 (mod 16).
    check_decrement_A: assert property (
        @(posedge clk) ($stable(B) && (A == $past(A) - 4'd1)) |-> (S == $past(S) - 4'd1)
    );

    // Swapping A and B across cycles leaves S unchanged (commutativity).
    check_swap_commutativity: assert property (
        @(posedge clk) (A == $past(B) && B == $past(A)) |-> (S == $past(S))
    );
endmodule