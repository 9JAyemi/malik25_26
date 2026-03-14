module top_module_sva (
    input  logic        clk,
    input  logic [31:0] a,
    input  logic [31:0] b,
    input  logic        select,
    input  logic [31:0] sum
);
    ///// Functional correctness /////
    // Sum matches the RTL ternary: select ? (a ^ b) : {31'b0, a[0]}.
    check_sum_function: assert property (
        @(posedge clk) sum == (select ? (a ^ b) : {31'b0, a[0]})
    );

    // When select=1, sum upper bits are bitwise XOR of a and b.
    check_select1_upper_bits_xor: assert property (
        @(posedge clk) select |-> (sum[31:1] == (a[31:1] ^ b[31:1]))
    );

    // When select=1, sum LSB equals a[0] ^ b[0].
    check_select1_lsb_xor: assert property (
        @(posedge clk) select |-> (sum[0] == (a[0] ^ b[0]))
    );

    // When select=0, sum upper bits are all zero.
    check_select0_upper_bits_zero: assert property (
        @(posedge clk) !select |-> (sum[31:1] == 31'b0)
    );

    // When select=0, sum LSB equals a[0].
    check_select0_lsb_is_a0: assert property (
        @(posedge clk) !select |-> (sum[0] == a[0])
    );

    ///// Stability and dependency /////
    // If inputs (a,b,select) are stable, sum must remain stable.
    check_sum_stable_when_inputs_stable: assert property (
        @(posedge clk) $stable({a,b,select}) |-> $stable(sum)
    );

    // Sum can only change if at least one of a, b, or select changes.
    check_sum_change_implies_input_change: assert property (
        @(posedge clk) $changed(sum) |-> ($changed(a) || $changed(b) || $changed(select))
    );

    // When select stays 0 and a is stable, changes on b must not affect sum.
    check_b_irrelevant_when_select0: assert property (
        @(posedge clk) (!select && $past(!select) && $stable(a) && $changed(b)) |-> $stable(sum)
    );

    // When select stays 0 and a[0] is stable, changes on a[31:1] must not affect sum.
    check_highbits_irrelevant_when_select0: assert property (
        @(posedge clk) (!select && $past(!select) && $changed(a) && $stable(a[0])) |-> $stable(sum)
    );

endmodule