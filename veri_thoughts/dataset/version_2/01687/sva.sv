module verilog_module_sva (
    input logic clk,
    input logic rst,
    input logic enable,
    input logic sampling_event,
    input logic test_expr,
    input logic prevConfigInvalid,
    input logic out
);
    // Clock: clk; Reset: rst (active-high, async). Sequential logic with enable; toggle or load sampling_event.

    // Reset drives out low.
    check_reset_out_low: assert property (
        @(posedge clk) rst |-> (out == 1'b0)
    );

    // When disabled, out holds its value.
    check_hold_when_disabled: assert property (
        @(posedge clk) disable iff (rst) (!enable) |-> $stable(out)
    );

    // When enabled and (test_expr && !prevConfigInvalid), out toggles.
    check_toggle_when_cond_true: assert property (
        @(posedge clk) disable iff (rst) (enable && test_expr && !prevConfigInvalid) |-> (out == !$past(out))
    );

    // When enabled and NOT (test_expr && !prevConfigInvalid), out loads sampling_event.
    check_load_sampling_when_cond_false: assert property (
        @(posedge clk) disable iff (rst) (enable && !(test_expr && !prevConfigInvalid)) |-> (out == sampling_event)
    );

    // Two consecutive toggle cycles return out to its 2-cycle-old value.
    check_double_toggle_returns_original: assert property (
        @(posedge clk) disable iff (rst)
            (enable && test_expr && !prevConfigInvalid && $past(enable && test_expr && !prevConfigInvalid))
            |-> (out == $past(out, 2))
    );

    // In toggle branch, if sampling_event equals previous out, the new out must differ from sampling_event.
    check_toggle_overrides_sampling_match: assert property (
        @(posedge clk) disable iff (rst)
            (enable && test_expr && !prevConfigInvalid && (sampling_event == $past(out)))
            |-> (out != sampling_event)
    );

    // In sample branch, if sampling_event equals previous out, out remains unchanged.
    check_sample_branch_stable_when_matches_past: assert property (
        @(posedge clk) disable iff (rst)
            (enable && !(test_expr && !prevConfigInvalid) && (sampling_event == $past(out)))
            |-> (out == $past(out))
    );

    // In sample branch, if sampling_event is inverse of previous out, out becomes inverse of previous out.
    check_sample_branch_toggle_when_opposite_past: assert property (
        @(posedge clk) disable iff (rst)
            (enable && !(test_expr && !prevConfigInvalid) && (sampling_event == !$past(out)))
            |-> (out == !$past(out))
    );

endmodule