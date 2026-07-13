module m_pc_reg_sva (
    input logic w_clock,
    input logic w_reset,
    input logic [7:0] w_bus_addr_in,
    output logic [7:0] r_bus_addr_out
);
    ///// Register behavior /////
    // Register r_bus_addr_out should hold the value of w_bus_addr_in on the positive edge of w_clock.
    register_update: assert property (
        @(posedge w_clock) disable iff (!w_reset) r_bus_addr_out == w_bus_addr_in
    );
    // Register r_bus_addr_out should be reset to 0 on the positive edge of w_clock when w_reset is asserted.
    register_reset: assert property (
        @(posedge w_clock) disable iff (!w_reset) (w_reset == 1'b1) |-> r_bus_addr_out == 8'b0
    );
endmodule