module manchester_assertions (
    input logic in,
    input logic out,
    input logic prev_in,
    input logic out_reg
);

    // Output continuously reflects the internal output register.
    check_out_matches_out_reg: assert property (
        @(posedge in) out === out_reg
    );

    // prev_in captures the high level present on each posedge of in.
    check_prev_in_captures_high: assert property (
        @(posedge in) 1'b1 |=> (prev_in === 1'b1)
    );

    // When prev_in was high, the toggle branch inverts out_reg.
    check_toggle_branch_updates_out_reg: assert property (
        @(posedge in) (prev_in === 1'b1) |=> (out_reg === ~$past(out_reg))
    );

    // When prev_in was not high, the load branch drives out_reg high.
    check_load_branch_updates_out_reg: assert property (
        @(posedge in) (prev_in !== 1'b1) |=> (out_reg === 1'b1)
    );

    // When prev_in was high, the observable output toggles.
    check_toggle_branch_updates_out: assert property (
        @(posedge in) (prev_in === 1'b1) |=> (out === ~$past(out))
    );

    // When prev_in was not high, the observable output becomes high.
    check_load_branch_updates_out: assert property (
        @(posedge in) (prev_in !== 1'b1) |=> (out === 1'b1)
    );

endmodule