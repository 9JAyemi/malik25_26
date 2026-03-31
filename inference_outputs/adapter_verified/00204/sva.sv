module debounce_sva (
    input logic pb_debounced,
    input logic pb,
    input logic clk,
    input logic [3:0] shift_reg
);

// pb_debounced must be low when the shift register is all zeros.
    check_debounced_low_when_shift_zero: assert property (
        @(posedge clk) (shift_reg == 4'b0000) |-> (pb_debounced == 1'b0)
    );

// pb_debounced must be high when the shift register is not all zeros.
    check_debounced_high_when_shift_nonzero: assert property (
        @(posedge clk) (shift_reg != 4'b0000) |-> (pb_debounced == 1'b1)
    );

// A sampled low pb must drive the next sampled shift register value to 0001.
    check_shift_after_low_pb: assert property (
        @(posedge clk) (pb == 1'b0) |=> (shift_reg == 4'b0001)
    );

// A sampled high pb must drive the next sampled shift register value to 0011.
    check_shift_after_high_pb: assert property (
        @(posedge clk) (pb == 1'b1) |=> (shift_reg == 4'b0011)
    );

endmodule
