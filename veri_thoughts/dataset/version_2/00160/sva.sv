module reg_module_sva (
    input logic       clk,
    input logic       reset,
    input logic       wenb,
    input logic [7:0] in_data,
    input logic [7:0] reg_out
);

    // Reset clears the register on the next sampled cycle.
    check_reset_clears_reg: assert property (
        @(posedge clk) reset |=> (reg_out == 8'h00)
    );

    // Reset has priority over write enable.
    check_reset_priority_over_write: assert property (
        @(posedge clk) (reset && wenb) |=> (reg_out == 8'h00)
    );

    // A write captures in_data into reg_out.
    check_write_updates_reg: assert property (
        @(posedge clk) disable iff (reset)
        wenb |=> (reg_out == $past(in_data))
    );

    // Without a write, the register holds its previous value.
    check_hold_without_write: assert property (
        @(posedge clk) disable iff (reset)
        !wenb |=> (reg_out == $past(reg_out))
    );

endmodule