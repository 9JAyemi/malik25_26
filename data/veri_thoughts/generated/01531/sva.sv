module add_sub_sva (
    input logic clk,          // External clock for SVA (RTL has no clock/reset)
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUB,
    input logic [3:0] Q
);
    // Q equals (A + B) when SUB is 0 (modulo-16)
    check_sum_path: assert property (
        @(posedge clk) (SUB == 1'b0) |-> (Q == (A + B)[3:0])
    );

    // Q equals (A - B) when SUB is 1 (modulo-16)
    check_diff_path: assert property (
        @(posedge clk) (SUB == 1'b1) |-> (Q == (A - B)[3:0])
    );

    // On SUB falling edge, Q reflects sum path
    check_q_on_sub_fall: assert property (
        @(posedge clk) $fell(SUB) |-> (Q == (A + B)[3:0])
    );

    // On SUB rising edge, Q reflects diff path
    check_q_on_sub_rise: assert property (
        @(posedge clk) $rose(SUB) |-> (Q == (A - B)[3:0])
    );

    // Add inverse: when SUB=0, (Q - B) mod 16 equals A
    check_add_inverse: assert property (
        @(posedge clk) (SUB == 1'b0) |-> ((Q - B)[3:0] == A)
    );

    // Sub inverse: when SUB=1, (Q + B) mod 16 equals A
    check_sub_inverse: assert property (
        @(posedge clk) (SUB == 1'b1) |-> ((Q + B)[3:0] == A)
    );

    // If B is zero, Q equals A regardless of SUB
    check_b_zero_transparency: assert property (
        @(posedge clk) (B == 4'd0) |-> (Q == A)
    );

    // If SUB=0 and A is zero, Q equals B
    check_a_zero_add_identity: assert property (
        @(posedge clk) (SUB == 1'b0 && A == 4'd0) |-> (Q == B)
    );

    // If SUB=1 and A equals B, Q is zero
    check_equal_operands_sub_zero: assert property (
        @(posedge clk) (SUB == 1'b1 && A == B) |-> (Q == 4'd0)
    );

    // If inputs are stable, output remains stable
    check_stability_when_inputs_stable: assert property (
        @(posedge clk) $stable(A) && $stable(B) && $stable(SUB) |-> $stable(Q)
    );
endmodule