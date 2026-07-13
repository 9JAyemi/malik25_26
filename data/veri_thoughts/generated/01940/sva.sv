module crc_module_sva (
    input  logic        clk,
    input  logic [8:0]  Output,
    input  integer      cyc,
    input  logic [63:0] crc,
    input  logic [31:0] sum
);
    // Clock: clk (posedge). No explicit reset; assertions use disable iff (1'b0).
    // Sequential LFSR (crc), accumulator (sum), and conditional Output at cyc==99.

    // cyc increments by 1 every cycle.
    check_cyc_increments: assert property (
        @(posedge clk) disable iff (1'b0) (!$isunknown($past(cyc))) |-> (cyc == $past(cyc) + 1)
    );

    // On cycle after cyc==0, crc is initialized to constant.
    check_crc_init_on_cyc0: assert property (
        @(posedge clk) disable iff (1'b0) (!$isunknown($past(cyc)) && ($past(cyc) == 0)) |-> (crc == 64'h5aef0c8d_d70a4497)
    );

    // On cycle after cyc==0, sum is initialized to 0.
    check_sum_init_on_cyc0: assert property (
        @(posedge clk) disable iff (1'b0) (!$isunknown($past(cyc)) && ($past(cyc) == 0)) |-> (sum == 32'h0)
    );

    // For all cycles except after cyc==0, crc updates via LFSR shift/xor.
    check_crc_lfsr_shift: assert property (
        @(posedge clk) disable iff (1'b0)
            (!$isunknown($past(cyc)) && ($past(cyc) != 0)) |-> (
                crc == { ($past(crc))[62:0], (($past(crc))[63] ^ ($past(crc))[2] ^ ($past(crc))[0]) }
            )
    );

    // When 10 < cyc < 90 (evaluated on previous cycle), sum updates by rotate-left-1 XOR zero-extended crc[8:0].
    check_sum_update_window: assert property (
        @(posedge clk) disable iff (1'b0)
            (!$isunknown($past(cyc)) && ($past(cyc) > 10) && ($past(cyc) < 90)) |-> (
                sum == { ($past(sum))[30:0], ($past(sum))[31] } ^ {23'h0, ($past(crc))[8:0]}
            )
    );

    // Outside the update window (and not after cyc==0), sum holds its previous value.
    check_sum_hold_outside_window: assert property (
        @(posedge clk) disable iff (1'b0)
            (!$isunknown($past(cyc)) && ($past(cyc) != 0) && !(($past(cyc) > 10) && ($past(cyc) < 90))) |-> (
                sum == $past(sum)
            )
    );

    // At cyc==99 (previous cycle), sum is not written and holds.
    check_sum_hold_at_cyc99: assert property (
        @(posedge clk) disable iff (1'b0)
            (!$isunknown($past(cyc)) && ($past(cyc) == 99)) |-> (sum == $past(sum))
    );

    // At cyc==99 with sum == magic, Output is 9'h4a.
    check_output_on_99_matches_sum_true: assert property (
        @(posedge clk) disable iff (1'b0)
            (!$isunknown($past(cyc)) && ($past(cyc) == 99) && ($past(sum) == 32'he8bbd130)) |-> (Output == 9'h4a)
    );

    // At cyc==99 with sum != magic, Output is 9'h55.
    check_output_on_99_matches_sum_false: assert property (
        @(posedge clk) disable iff (1'b0)
            (!$isunknown($past(cyc)) && ($past(cyc) == 99) && ($past(sum) != 32'he8bbd130)) |-> (Output == 9'h55)
    );

    // On all cycles where previous cyc != 99, Output does not change.
    check_output_stable_when_not_99: assert property (
        @(posedge clk) disable iff (1'b0)
            (!$isunknown($past(cyc)) && ($past(cyc) != 99)) |-> (Output === $past(Output))
    );

    // On the cycle after cyc==99, Output is one of the two defined values.
    check_output_values_on_99: assert property (
        @(posedge clk) disable iff (1'b0)
            (!$isunknown($past(cyc)) && ($past(cyc) == 99)) |-> (Output inside {9'h4a, 9'h55})
    );

endmodule