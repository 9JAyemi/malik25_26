module r_TX_BUF_OBJ7_BYTE_0_assertions (
    input logic [7:0] reg_0x6C,
    input logic reset,
    input logic wenb,
    input logic [7:0] in_data,
    input logic clk
);

    // Reset clears the register on the next clock.
    check_reset_clears_reg: assert property (
        @(posedge clk) reset |=> (reg_0x6C == 8'h00)
    );

    // A low write enable loads the input byte.
    check_write_captures_input: assert property (
        @(posedge clk) disable iff (reset) (!wenb) |=> (reg_0x6C == $past(in_data))
    );

    // A high write enable leaves the register unchanged.
    check_no_write_holds_value: assert property (
        @(posedge clk) disable iff (reset) wenb |=> (reg_0x6C == $past(reg_0x6C))
    );

    // Any register change must be caused by reset or an enabled write.
    check_reg_change_has_cause: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        (reg_0x6C != $past(reg_0x6C)) |-> ($past(reset) || !$past(wenb))
    );

endmodule