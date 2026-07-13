module sparc_ifu_cmp35_sva (
    input logic [34:0] a,
    input logic [34:0] b,
    input logic        valid,
    input logic        hit
);
    // Combinational compare; no clock/reset in RTL; sample using $global_clock.

    // hit equals (a==b) & valid.
    check_hit_function: assert property (
        @($global_clock) hit == ((a == b) & valid)
    );

    // When valid is low, hit must be 0.
    check_no_hit_when_valid_low: assert property (
        @($global_clock) !valid |-> (hit == 1'b0)
    );

    // When valid is high and a equals b, hit must be 1.
    check_hit_when_valid_and_equal: assert property (
        @($global_clock) (valid && (a == b)) |-> (hit == 1'b1)
    );

    // When valid is high and a not equal b, hit must be 0.
    check_no_hit_when_valid_and_not_equal: assert property (
        @($global_clock) (valid && (a != b)) |-> (hit == 1'b0)
    );

    // If hit is 1 then valid is 1 and a equals b.
    check_hit_implies_valid_and_equal: assert property (
        @($global_clock) hit |-> (valid && (a == b))
    );

    // If a, b, and valid are stable, hit remains stable.
    check_stability: assert property (
        @($global_clock) ($stable(a) && $stable(b) && $stable(valid)) |-> $stable(hit)
    );

    // Any change on hit must be caused by a, b, or valid changing.
    check_hit_change_needs_input_change: assert property (
        @($global_clock) $changed(hit) |-> ($changed(a) || $changed(b) || $changed(valid))
    );
endmodule