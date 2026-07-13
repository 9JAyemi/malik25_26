module test_eval_generic_sva (
    input logic clk,
    input logic [7:0] data,
    input logic out_bit_def,
    input logic out_bit_ovr
);

// out_bit_def is high when the upper nibble has 4 or more ones.
    check_def_high_when_upper_nibble_ge4: assert property (
        @(posedge clk) (|data[7:4] >= 4'b1000) |-> (out_bit_def == 1'b1)
    );

// out_bit_def is low when the upper nibble has fewer than 4 ones.
    check_def_low_when_upper_nibble_lt4: assert property (
        @(posedge clk) (|data[7:4] < 4'b1000) |-> (out_bit_def == 1'b0)
    );

// out_bit_ovr follows data[4].
    check_ovr_follows_data4: assert property (
        @(posedge clk) (out_bit_ovr == data[4])
    );

// A high out_bit_def requires the upper nibble to have 4 or more ones.
    check_def_implies_upper_nibble_ge4: assert property (
        @(posedge clk) (out_bit_def == 1'b1) |-> (|data[7:4] >= 4'b1000)
    );

// A low out_bit_def requires the upper nibble to have fewer than 4 ones.
    check_def0_implies_upper_nibble_lt4: assert property (
        @(posedge clk) (out_bit_def == 1'b0) |-> (|data[7:4] < 4'b1000)
    );

// A high out_bit_ovr requires data[4] to be high.
    check_ovr1_implies_data4: assert property (
        @(posedge clk) (out_bit_ovr == 1'b1) |-> (data[4] == 1'b1)
    );

// A low out_bit_ovr requires data[4] to be low.
    check_ovr0_implies_data4: assert property (
        @(posedge clk) (out_bit_ovr == 1'b0) |-> (data[4] == 1'b0)
    );

endmodule
