module bit_counter_sva (
    input logic clk,
    input logic [3:0] in,
    input logic count
);

    // Count is the parity of the four input bits.
    check_count_matches_parity: assert property (
        @(posedge clk) count == (in[0] ^ in[1] ^ in[2] ^ in[3])
    );

    // Zero or four asserted input bits drive count low.
    check_zero_or_four_ones_drive_low: assert property (
        @(posedge clk) ((in == 4'b0000) || (in == 4'b1111)) |-> (count == 1'b0)
    );

    // Any one-hot input drives count high.
    check_one_hot_drives_high: assert property (
        @(posedge clk) (in inside {4'b0001, 4'b0010, 4'b0100, 4'b1000}) |-> (count == 1'b1)
    );

    // Any two-hot input drives count low.
    check_two_ones_drive_low: assert property (
        @(posedge clk) (in inside {4'b0011, 4'b0101, 4'b0110, 4'b1001, 4'b1010, 4'b1100}) |-> (count == 1'b0)
    );

    // Any three-hot input drives count high.
    check_three_ones_drive_high: assert property (
        @(posedge clk) (in inside {4'b0111, 4'b1011, 4'b1101, 4'b1110}) |-> (count == 1'b1)
    );

endmodule