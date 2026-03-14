module ddr2_ex_lfsr8_sva #(
    parameter int unsigned seed = 32
) (
    input  logic        clk,
    input  logic        reset_n,
    input  logic        enable,
    input  logic        pause,
    input  logic        load,
    input  logic [7:0]  data,
    input  logic [7:0]  ldata
);
    localparam logic [7:0] SEED8 = seed[7:0];

    // While reset is asserted, data must drive the seed value.
    reset_drives_seed: assert property (
        @(posedge clk) !reset_n |-> (data == SEED8)
    );

    // When enable is LOW, next data must be the seed.
    next_seed_when_disabled: assert property (
        @(posedge clk) disable iff (!reset_n) (!enable) |=> (data == SEED8)
    );

    // With enable and load HIGH, next data must capture ldata.
    next_load_data: assert property (
        @(posedge clk) disable iff (!reset_n) (enable && load) |=> (data == $past(ldata))
    );

    // Load has priority over pause when both are HIGH.
    load_over_pause: assert property (
        @(posedge clk) disable iff (!reset_n) (enable && load && pause) |=> (data == $past(ldata))
    );

    // When enabled, no load, and paused, data must hold its value.
    hold_when_paused: assert property (
        @(posedge clk) disable iff (!reset_n) (enable && !load && pause) |=> (data == $past(data))
    );

    // When enabled, no load, and not paused, perform the LFSR step.
    lfsr_step_vector_update: assert property (
        @(posedge clk) disable iff (!reset_n)
        (enable && !load && !pause) |=> (
            data == {
                $past(data[6]),                         // next[7]
                $past(data[5]),                         // next[6]
                $past(data[4]),                         // next[5]
                $past(data[3]) ^ $past(data[7]),        // next[4]
                $past(data[2]) ^ $past(data[7]),        // next[3]
                $past(data[1]) ^ $past(data[7]),        // next[2]
                $past(data[0]),                         // next[1]
                $past(data[7])                          // next[0]
            }
        )
    );

    // Bit[2] tap uses XOR with bit[7] on LFSR step.
    tap_bit2_xor7: assert property (
        @(posedge clk) disable iff (!reset_n)
        (enable && !load && !pause) |=> (data[2] == ($past(data[1]) ^ $past(data[7])))
    );

    // Bit[3] tap uses XOR with bit[7] on LFSR step.
    tap_bit3_xor7: assert property (
        @(posedge clk) disable iff (!reset_n)
        (enable && !load && !pause) |=> (data[3] == ($past(data[2]) ^ $past(data[7])))
    );

    // Bit[4] tap uses XOR with bit[7] on LFSR step.
    tap_bit4_xor7: assert property (
        @(posedge clk) disable iff (!reset_n)
        (enable && !load && !pause) |=> (data[4] == ($past(data[3]) ^ $past(data[7])))
    );

    // Any data change must be due to disable, load, or LFSR step in the prior cycle.
    data_change_has_valid_cause: assert property (
        @(posedge clk) disable iff (!reset_n)
        $changed(data) |-> (
            !$past(enable) ||
            ($past(enable) && $past(load)) ||
            ($past(enable) && !$past(load) && !$past(pause))
        )
    );

    // If enable is LOW and load is HIGH, seed still wins next cycle.
    disabled_masks_load: assert property (
        @(posedge clk) disable iff (!reset_n)
        (!enable && load) |=> (data == SEED8)
    );

endmodule