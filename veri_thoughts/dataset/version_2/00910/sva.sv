module binary_to_gray_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] bin,
    input logic [7:0] gray
);
    ///// Reset behavior /////
    // When reset is asserted at the clock edge, gray must be all zeros.
    reset_forces_gray_zero: assert property (
        @(posedge clk) reset |-> (gray == 8'b0)
    );

    ///// Binary-to-Gray mapping (registered, 1-cycle latency) /////
    // After a non-reset cycle, gray equals the Gray-encoded value of prior bin.
    check_gray_vector_mapping: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset) |-> (gray == {
                $past(bin[7]),
                ($past(bin[7]) ^ $past(bin[6])),
                ($past(bin[6]) ^ $past(bin[5])),
                ($past(bin[5]) ^ $past(bin[4])),
                ($past(bin[4]) ^ $past(bin[3])),
                ($past(bin[3]) ^ $past(bin[2])),
                ($past(bin[2]) ^ $past(bin[1])),
                ($past(bin[1]) ^ $past(bin[0]))
            })
    );

    // MSB of gray equals prior bin[7].
    check_gray7_maps_bin7: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset) |-> (gray[7] == $past(bin[7]))
    );

    // gray[6] equals prior bin[7] XOR bin[6].
    check_gray6_maps_bin76: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset) |-> (gray[6] == ($past(bin[7]) ^ $past(bin[6])))
    );

    // gray[5] equals prior bin[6] XOR bin[5].
    check_gray5_maps_bin65: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset) |-> (gray[5] == ($past(bin[6]) ^ $past(bin[5])))
    );

    // gray[4] equals prior bin[5] XOR bin[4].
    check_gray4_maps_bin54: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset) |-> (gray[4] == ($past(bin[5]) ^ $past(bin[4])))
    );

    // gray[3] equals prior bin[4] XOR bin[3].
    check_gray3_maps_bin43: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset) |-> (gray[3] == ($past(bin[4]) ^ $past(bin[3])))
    );

    // gray[2] equals prior bin[3] XOR bin[2].
    check_gray2_maps_bin32: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset) |-> (gray[2] == ($past(bin[3]) ^ $past(bin[2])))
    );

    // gray[1] equals prior bin[2] XOR bin[1].
    check_gray1_maps_bin21: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset) |-> (gray[1] == ($past(bin[2]) ^ $past(bin[1])))
    );

    // gray[0] equals prior bin[1] XOR bin[0].
    check_gray0_maps_bin10: assert property (
        @(posedge clk) disable iff (reset)
            $past(!reset) |-> (gray[0] == ($past(bin[1]) ^ $past(bin[0])))
    );
endmodule