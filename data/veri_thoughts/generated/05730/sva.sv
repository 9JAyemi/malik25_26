module comb_logic_assertions (
    input logic a,
    input logic b,
    input logic select,
    input logic clk,
    input logic out_always_ff
);

    // Output captures the prior-cycle selected function of a and b.
    check_registered_mux_function: assert property (
        @(posedge clk)
        1'b1 |=> (out_always_ff == ($past(select)
                                   ? ($past(a) | $past(b))
                                   : (($past(a) & ~$past(b)) | (~$past(a) & $past(b))))
        )
    );

    // When select is low, output captures the prior XOR function.
    check_xor_path: assert property (
        @(posedge clk)
        !select |=> (out_always_ff == (($past(a) & ~$past(b)) | (~$past(a) & $past(b)))
        )
    );

    // When select is high, output captures the prior OR function.
    check_or_path: assert property (
        @(posedge clk)
        select |=> (out_always_ff == ($past(a) | $past(b)))
    );

    // With select low and equal inputs, output is low on the next clock.
    check_xor_equal_inputs_zero: assert property (
        @(posedge clk)
        (!select && (a == b)) |=> (out_always_ff == 1'b0)
    );

    // With select low and different inputs, output is high on the next clock.
    check_xor_different_inputs_one: assert property (
        @(posedge clk)
        (!select && (a != b)) |=> (out_always_ff == 1'b1)
    );

    // With select high and both inputs low, output is low on the next clock.
    check_or_both_low_zero: assert property (
        @(posedge clk)
        (select && !a && !b) |=> (out_always_ff == 1'b0)
    );

    // With select high and any input high, output is high on the next clock.
    check_or_any_high_one: assert property (
        @(posedge clk)
        (select && (a || b)) |=> (out_always_ff == 1'b1)
    );

endmodule