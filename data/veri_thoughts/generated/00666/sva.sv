module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] sum,
    input logic [7:0] carry_out
);
    ///// Combinational half-adder behavior (clocked checks) /////
    // Sum must equal bitwise XOR of a and b.
    check_sum_is_xor: assert property (
        @(posedge clk) disable iff (reset) sum == (a ^ b)
    );
    // Carry_out must equal bitwise AND of a and b.
    check_carry_is_and: assert property (
        @(posedge clk) disable iff (reset) carry_out == (a & b)
    );
    // No bit can have both sum and carry_out asserted simultaneously.
    check_sum_and_carry_mutex: assert property (
        @(posedge clk) disable iff (reset) (sum & carry_out) == 8'b0
    );
    // Carry_out bits can only be 1 where a has 1s.
    check_carry_subset_of_a: assert property (
        @(posedge clk) disable iff (reset) (carry_out & ~a) == 8'b0
    );
    // Carry_out bits can only be 1 where b has 1s.
    check_carry_subset_of_b: assert property (
        @(posedge clk) disable iff (reset) (carry_out & ~b) == 8'b0
    );
    // sum XOR carry_out equals bitwise OR of a and b.
    check_sum_xor_carry_eq_or: assert property (
        @(posedge clk) disable iff (reset) (sum ^ carry_out) == (a | b)
    );
    // sum OR carry_out equals bitwise OR of a and b.
    check_sum_or_carry_eq_or: assert property (
        @(posedge clk) disable iff (reset) (sum | carry_out) == (a | b)
    );
    // From sum and a, we can recover b (XOR involution).
    check_recover_b_from_sum_a: assert property (
        @(posedge clk) disable iff (reset) (sum ^ a) == b
    );
    // From sum and b, we can recover a (XOR involution).
    check_recover_a_from_sum_b: assert property (
        @(posedge clk) disable iff (reset) (sum ^ b) == a
    );
    // If a and b are stable cycle-to-cycle, sum and carry_out must be stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge clk) disable iff (reset) ($stable(a) && $stable(b)) |-> ($stable(sum) && $stable(carry_out))
    );
    // sum masked by a equals a AND NOT b.
    check_sum_and_a_mask: assert property (
        @(posedge clk) disable iff (reset) (sum & a) == (a & ~b)
    );
    // sum masked by b equals b AND NOT a.
    check_sum_and_b_mask: assert property (
        @(posedge clk) disable iff (reset) (sum & b) == (b & ~a)
    );
endmodule