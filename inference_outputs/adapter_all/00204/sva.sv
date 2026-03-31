module debounce_sva (
    input logic pb_debounced,
    input logic pb,
    input logic clk,
    input logic [3:0] shift_reg
);
    // pb_debounced equals (shift_reg != 4'b0000).
    check_debounced_definition: assert property (
        @(posedge clk) pb_debounced == (shift_reg != 4'b0000)
    );

    // If shift_reg is all zeros, pb_debounced must be 0.
    check_zero_reg_implies_debounced_low: assert property (
        @(posedge clk) (shift_reg == 4'b0000) |-> (pb_debounced == 1'b0)
    );

    // If shift_reg is not all zeros, pb_debounced must be 1.
    check_nonzero_reg_implies_debounced_high: assert property (
        @(posedge clk) (shift_reg != 4'b0000) |-> (pb_debounced == 1'b1)
    );

    // pb_debounced low implies shift_reg is all zeros.
    check_debounced_low_implies_zero_reg: assert property (
        @(posedge clk) (pb_debounced == 1'b0) |-> (shift_reg == 4'b0000)
    );

    // pb_debounced high implies shift_reg is not all zeros.
    check_debounced_high_implies_nonzero_reg: assert property (
        @(posedge clk) (pb_debounced == 1'b1) |-> (shift_reg != 4'b0000)
    );

    // pb_debounced equals (any bit of shift_reg is 1).
    check_debounced_anybit: assert property (
        @(posedge clk) pb_debounced == |shift_reg
    );

    // pb_debounced equals (no bit of shift_reg is 0).
    check_debounced_nobit0: assert property (
        @(posedge clk) pb_debounced == ~&shift_reg
    );

    // pb_debounced equals (not all bits of shift_reg are 0).
    check_debounced_notall0: assert property (
        @(posedge clk) pb_debounced == ~(&shift_reg == 4'b0000)
    );

    // pb_debounced equals (not all bits of shift_reg are 1).
    check_debounced_notall1: assert property (
        @(posedge clk) pb_debounced == ~(&shift_reg == 4'b1111)
    );

    // pb_debounced equals (shift_reg is not 0000 or 1111).
    check_debounced_not0or1: assert property (
        @(posedge clk) pb_debounced == ~(shift_reg == 4'b0000 || shift_reg == 4'b1111)
    );
endmodule