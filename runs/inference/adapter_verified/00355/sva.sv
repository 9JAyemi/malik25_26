module m_pc_reg_sva (
    input logic [7:0] r_bus_addr_out,
    input logic [7:0] w_bus_addr_in,
    input logic w_clock,
    input logic w_reset
);

// On a clock edge with reset asserted, the output is cleared to zero.
    check_reset_clears_output: assert property (
        @(posedge w_clock) w_reset |-> (r_bus_addr_out == 8'h00)
    );

// On a clock edge with reset deasserted, the output captures the prior input value.
    check_capture_on_no_reset: assert property (
        @(posedge w_clock) disable iff (w_reset) 1'b1 |=> (r_bus_addr_out == $past(w_bus_addr_in))
    );

// If reset is held high across consecutive clock edges, the output remains zero.
    check_zero_held_when_reset_held: assert property (
        @(posedge w_clock) (w_reset && $past(w_reset)) |-> (r_bus_addr_out == 8'h00)
    );

// If reset is deasserted and the input is stable across consecutive clock edges, the output remains stable.
    check_stable_output_when_input_stable: assert property (
        @(posedge w_clock) disable iff (w_reset) $stable(w_bus_addr_in) |=> $stable(r_bus_addr_out)
    );

endmodule
