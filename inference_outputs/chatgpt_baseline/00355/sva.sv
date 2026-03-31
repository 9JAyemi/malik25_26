module m_pc_reg_sva (
    input logic [7:0] r_bus_addr_out,
    input logic [7:0] w_bus_addr_in,
    input logic       w_clock,
    input logic       w_reset
);

    // A reset-active clock edge drives the register output to zero.
    check_reset_clears_output: assert property (
        @(posedge w_clock) disable iff ($initstate)
        $past(w_reset) |-> (r_bus_addr_out == 8'b0)
    );

    // A non-reset clock edge loads the previous input value into the register.
    check_loads_input_when_not_reset: assert property (
        @(posedge w_clock) disable iff ($initstate)
        !$past(w_reset) |-> (r_bus_addr_out == $past(w_bus_addr_in))
    );

    // The register output always matches the RTL next-state function.
    check_exact_next_state_function: assert property (
        @(posedge w_clock) disable iff ($initstate)
        r_bus_addr_out == ($past(w_reset) ? 8'b0 : $past(w_bus_addr_in))
    );

endmodule