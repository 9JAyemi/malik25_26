module r_CONFIG_STANDARD_OUTPUT_sva (
    input logic [7:0] reg_0x18,
    input logic reset,
    input logic wenb,
    input logic [7:0] in_data,
    input logic clk
);

    // Reset drives the register to 0 on the next sampled cycle.
    check_reset_clears_register: assert property (
        @(posedge clk) reset |=> (reg_0x18 == 8'h00)
    );

    // Reset takes priority over a simultaneous active-low write.
    check_reset_overrides_write: assert property (
        @(posedge clk) (reset && (wenb == 1'b0)) |=> (reg_0x18 == 8'h00)
    );

    // An active-low write captures in_data into the register.
    check_write_captures_in_data: assert property (
        @(posedge clk) disable iff (reset) (wenb == 1'b0) |=> (reg_0x18 == $past(in_data))
    );

    // With write disabled, the register holds its previous value.
    check_hold_without_write: assert property (
        @(posedge clk) disable iff (reset) (wenb == 1'b1) |=> (reg_0x18 == $past(reg_0x18))
    );

endmodule