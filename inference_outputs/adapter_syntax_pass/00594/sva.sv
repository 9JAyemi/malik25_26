module top_module_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic        select,
    input logic [31:0] sum
);

    // When select is high, sum must equal the 32-bit addition of a and b.
    check_select_high_adds_inputs: assert property (
        @(posedge clk) (select == 1'b1) |-> (sum == (a + b))
    );

    // When select is low, sum must be zero-extended bit 0 of a.
    check_select_low_uses_a_lsb: assert property (
        @(posedge clk) (select == 1'b0) |-> (sum == {31'b0, a[0]})
    );

    // With a and b equal and select high, sum must equal the doubled value.
    check_select_high_equal_inputs_double: assert property (
        @(posedge clk) ((select == 1'b1) && (a == b)) |-> (sum == (a + a))
    );

    // With a and b equal and select low, sum must equal a[0] repeated 32 times.
    check_select_low_equal_inputs_repeat_lsb: assert property (
        @(posedge clk) ((select == 1'b0) && (a == b)) |-> (sum == {31{a[0]}})
    );

    // With a and b both zero, sum must be zero regardless of select.
    check_zero_inputs_zero_output: assert property (
        @(posedge clk) ((a == 32'h0) && (b == 32'h0)) |-> (sum == 32'h0)
    );

    // With a zero and b equal to a, sum must equal a regardless of select.
    check_a_zero_b_equal_a_passthrough: assert property (
        @(posedge clk) ((a == 32'h0) && (b == a)) |-> (sum == a)
    );

    // With a zero and b equal to ~a, sum must equal ~a regardless of select.
    check_a_zero_b_complement_a_passthrough: assert property (
        @(posedge clk) ((a == 32'h0) && (b == ~a)) |-> (sum == ~a)
    );

    // With a equal to b and b equal to ~a, sum must be all ones regardless of select.
    check_equal_inputs_complement_all_ones: assert property (
        @(posedge clk) ((a == b) && (b == ~a)) |-> (sum == 32'hFFFF_FFFF)
    );

endmodule