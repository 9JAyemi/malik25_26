module debounce_sva (
    input logic pb_debounced,
    input logic pb,
    input logic clk,
    input logic [3:0] shift_reg
);

    // pb_debounced must match the RTL's comparison of shift_reg to zero.
    check_debounced_matches_shift_reg: assert property (
        @(posedge clk) pb_debounced == ((shift_reg == 4'b0000) ? 1'b0 : 1'b1)
    );

    // A zero shift register must drive pb_debounced low.
    check_zero_shift_reg_drives_low: assert property (
        @(posedge clk) (shift_reg == 4'b0000) |-> (pb_debounced == 1'b0)
    );

    // A nonzero shift register must drive pb_debounced high.
    check_nonzero_shift_reg_drives_high: assert property (
        @(posedge clk) (shift_reg != 4'b0000) |-> (pb_debounced == 1'b1)
    );

    // pb_debounced can only be high when the shift register is nonzero.
    check_high_output_requires_nonzero_shift_reg: assert property (
        @(posedge clk) (pb_debounced == 1'b1) |-> (shift_reg != 4'b0000)
    );

    // pb_debounced can only be low when the shift register is zero.
    check_low_output_requires_zero_shift_reg: assert property (
        @(posedge clk) (pb_debounced == 1'b0) |-> (shift_reg == 4'b0000)
    );

endmodule