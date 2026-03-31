module shift_register_sva (
    input logic clk,
    input logic [7:0] data,
    input logic [7:0] shifted_data
);

    // The register shifts previous bits toward the MSB and loads data[7] into bit 0.
    check_shift_update_whole: assert property (
        @(posedge clk) disable iff ($initstate)
        shifted_data == {$past(shifted_data[6:0]), $past(data[7])}
    );

    // Bit 0 captures the previous cycle's data[7].
    check_lsb_captures_data7: assert property (
        @(posedge clk) disable iff ($initstate)
        shifted_data[0] == $past(data[7])
    );

    // Bits [7:1] come from the previous cycle's bits [6:0].
    check_upper_bits_shift: assert property (
        @(posedge clk) disable iff ($initstate)
        shifted_data[7:1] == $past(shifted_data[6:0])
    );

endmodule