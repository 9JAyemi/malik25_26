module r_FAULT_STATUS_sva (
    input logic [7:0] reg_0x1F,
    input logic reset,
    input logic wenb,
    input logic [7:0] in_data,
    input logic clk
);

    // Reset clears the register on the next clock.
    check_reset_clears_register: assert property (
        @(posedge clk) reset |=> (reg_0x1F == 8'h00)
    );

    // A low write enable loads the input byte.
    check_write_loads_register: assert property (
        @(posedge clk) disable iff (reset)
        (wenb == 1'b0) |=> (reg_0x1F == $past(in_data))
    );

    // A high write enable holds the previous register value.
    check_hold_when_write_disabled: assert property (
        @(posedge clk) disable iff (reset)
        (wenb == 1'b1) |=> (reg_0x1F == $past(reg_0x1F))
    );

endmodule