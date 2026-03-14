module top_module_sva (
    input logic CLK,                // External clock for assertions (RTL has no clock/reset)
    input logic [31:0] a,
    input logic [31:0] b,
    input logic sub,
    input logic select,
    input logic [31:0] final_output
);
    // final_output must be a+b when select is 0.
    check_select0_sum: assert property (
        @(posedge CLK) (select == 1'b0) |-> (final_output == (a + b))
    );

    // final_output must be ~(a-b) when select is 1.
    check_select1_inverted_sub: assert property (
        @(posedge CLK) (select == 1'b1) |-> (final_output == ~(a - b))
    );

    // Combined functional relation for all cases.
    check_function_combined: assert property (
        @(posedge CLK) final_output == (select ? ~(a - b) : (a + b))
    );

    // Internal control ties sub to select.
    check_sub_equals_select: assert property (
        @(posedge CLK) sub == select
    );

    // If a,b,select are stable, final_output must be stable.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge CLK) $stable(a) && $stable(b) && $stable(select) |-> $stable(final_output)
    );

    // With select=0 stable and b stable, a increment by 1 causes final_output to increment by 1.
    inc_a_select0_increases_sum: assert property (
        @(posedge CLK) (select == 1'b0) && ($past(select) == 1'b0) && $stable(b) && (a == $past(a) + 32'd1)
        |-> (final_output == $past(final_output) + 32'd1)
    );

    // With select=0 stable and a stable, b increment by 1 causes final_output to increment by 1.
    inc_b_select0_increases_sum: assert property (
        @(posedge CLK) (select == 1'b0) && ($past(select) == 1'b0) && $stable(a) && (b == $past(b) + 32'd1)
        |-> (final_output == $past(final_output) + 32'd1)
    );

    // With select=1 stable and b stable, a increment by 1 causes final_output to decrement by 1.
    inc_a_select1_decreases_inverted_sub: assert property (
        @(posedge CLK) (select == 1'b1) && ($past(select) == 1'b1) && $stable(b) && (a == $past(a) + 32'd1)
        |-> (final_output == $past(final_output) - 32'd1)
    );

    // With select=1 stable and a stable, b increment by 1 causes final_output to increment by 1.
    inc_b_select1_increases_inverted_sub: assert property (
        @(posedge CLK) (select == 1'b1) && ($past(select) == 1'b1) && $stable(a) && (b == $past(b) + 32'd1)
        |-> (final_output == $past(final_output) + 32'd1)
    );

    // For select=1 and a==b, final_output must be all 1s.
    select1_equal_inputs_all_ones: assert property (
        @(posedge CLK) (select == 1'b1) && (a == b) |-> (final_output == 32'hFFFF_FFFF)
    );

    // For select=0 and b==0, final_output must pass through a.
    select0_b_zero_passthrough_a: assert property (
        @(posedge CLK) (select == 1'b0) && (b == 32'd0) |-> (final_output == a)
    );

    // For select=0 and a==0, final_output must pass through b.
    select0_a_zero_passthrough_b: assert property (
        @(posedge CLK) (select == 1'b0) && (a == 32'd0) |-> (final_output == b)
    );
endmodule