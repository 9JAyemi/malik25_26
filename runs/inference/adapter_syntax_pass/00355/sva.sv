module m_pc_reg_sva (
    input logic [7:0] r_bus_addr_out,
    input logic [7:0] w_bus_addr_in,
    input logic w_clock,
    input logic w_reset
);

    // Reset forces the registered output to zero on the next clock.
    check_reset_clears_output: assert property (
        @(posedge w_clock) w_reset |=> (r_bus_addr_out == 8'h00)
    );

    // With reset low, the output captures the input on the next clock.
    check_capture_on_no_reset: assert property (
        @(posedge w_clock) disable iff (w_reset) 1'b1 |=> (r_bus_addr_out == $past(w_bus_addr_in))
    );

    // The output always matches the input from the previous clock edge.
    check_output_matches_previous_input: assert property (
        @(posedge w_clock) 1'b1 |=> (r_bus_addr_out == $past(w_bus_addr_in))
    );

endmodule