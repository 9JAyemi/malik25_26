module r_RX_BUF_OBJ3_BYTE_3_sva (
    input logic [7:0] reg_0x3F,
    input logic reset,
    input logic wenb,
    input logic [7:0] in_data,
    input logic clk
);

    // Sampled state must match the RTL update function from the prior cycle.
    check_transition_matches_rtl: assert property (
        @(posedge clk) disable iff ($initstate)
        reg_0x3F == ($past(reset) ? 8'h00 : ($past(wenb) ? $past(reg_0x3F) : $past(in_data)))
    );

    // A reset cycle clears the register to zero.
    check_reset_clears_reg: assert property (
        @(posedge clk) disable iff ($initstate)
        reset |=> (reg_0x3F == 8'h00)
    );

    // When wenb is low, the register captures in_data.
    check_write_captures_input: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !wenb |=> (reg_0x3F == $past(in_data))
    );

    // When wenb is high, the register holds its value.
    check_hold_when_wenb_high: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        wenb |=> (reg_0x3F == $past(reg_0x3F))
    );

    // The register only changes after reset or a write cycle.
    check_change_requires_reset_or_write: assert property (
        @(posedge clk) disable iff ($initstate)
        (reg_0x3F != $past(reg_0x3F)) |-> ($past(reset) || !$past(wenb))
    );

endmodule