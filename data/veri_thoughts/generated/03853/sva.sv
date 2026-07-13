module d_m_areg_sva (
    input logic         clk,
    input logic         rst,
    input logic [143:0] d_flits_m,
    input logic         v_d_flits_m,
    input logic         mem_done_access,
    input logic [175:0] d_m_areg_flits,
    input logic         v_d_m_areg_flits,
    input logic         d_m_areg_state
);

    // Valid output always matches the state output.
    check_valid_matches_state: assert property (
        @(posedge clk)
        v_d_m_areg_flits == d_m_areg_state
    );

    // Reset synchronously clears data and deasserts valid/state.
    check_reset_clears_outputs: assert property (
        @(posedge clk)
        rst |=> (!v_d_m_areg_flits && !d_m_areg_state && (d_m_areg_flits == 176'h0))
    );

    // mem_done_access synchronously clears data and deasserts valid/state.
    check_mem_done_clears_outputs: assert property (
        @(posedge clk)
        mem_done_access |=> (!v_d_m_areg_flits && !d_m_areg_state && (d_m_areg_flits == 176'h0))
    );

    // A valid input load sets state and valid on the next cycle.
    check_load_sets_state_and_valid: assert property (
        @(posedge clk) disable iff (rst)
        (!mem_done_access && v_d_flits_m) |=> (d_m_areg_state && v_d_m_areg_flits)
    );

    // A valid input load captures the lower 144 bits on the next cycle.
    check_load_captures_lower_flits: assert property (
        @(posedge clk) disable iff (rst)
        (!mem_done_access && v_d_flits_m) |=> (d_m_areg_flits[143:0] == $past(d_flits_m))
    );

    // A valid input load zero-extends the upper 32 bits.
    check_load_zero_extends_upper_flits: assert property (
        @(posedge clk) disable iff (rst)
        (!mem_done_access && v_d_flits_m) |=> (d_m_areg_flits[175:144] == 32'h0)
    );

    // Without a clear or load, the outputs hold their previous values.
    check_idle_holds_outputs: assert property (
        @(posedge clk) disable iff (rst)
        (!mem_done_access && !v_d_flits_m) |=> ($stable(d_m_areg_flits) &&
                                                $stable(v_d_m_areg_flits) &&
                                                $stable(d_m_areg_state))
    );

    // Once set, state and valid remain asserted until a clear occurs.
    check_state_is_sticky_until_clear: assert property (
        @(posedge clk) disable iff (rst)
        (d_m_areg_state && !mem_done_access) |=> (d_m_areg_state && v_d_m_areg_flits)
    );

endmodule