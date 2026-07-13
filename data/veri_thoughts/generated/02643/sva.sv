module ram_controller_ex_lfsr8_sva #(
    parameter int seed = 32
) (
    input logic clk,
    input logic reset_n,
    input logic enable,
    input logic pause,
    input logic load,
    input logic [7:0] data,
    input logic [7:0] ldata,
    input logic [7:0] lfsr_data
);
    // Clock: clk; Reset: reset_n (active-low, async). Sequential LFSR with enable/load/pause gating.
    localparam logic [7:0] SEED8 = seed[7:0];

    // Output data must mirror internal lfsr_data at all times.
    check_data_mirrors_lfsr: assert property (
        @(posedge clk) disable iff (!reset_n) data == lfsr_data
    );

    // While reset is asserted, state/output must be SEED8.
    check_reset_drives_seed: assert property (
        @(posedge clk) !reset_n |-> (lfsr_data == SEED8) && (data == SEED8)
    );

    // When enable is LOW, next state must be SEED8.
    check_disable_forces_seed_state: assert property (
        @(posedge clk) disable iff (!reset_n) (!enable) |=> (lfsr_data == SEED8)
    );

    // When enable is LOW, next output must be SEED8.
    check_disable_forces_seed_output: assert property (
        @(posedge clk) disable iff (!reset_n) (!enable) |=> (data == SEED8)
    );

    // When enabled and load is HIGH, next state loads ldata (pause ignored).
    check_load_updates_state: assert property (
        @(posedge clk) disable iff (!reset_n) (enable && load) |=> (lfsr_data == $past(ldata))
    );

    // When enabled and load is HIGH, next output reflects loaded ldata.
    check_load_updates_output: assert property (
        @(posedge clk) disable iff (!reset_n) (enable && load) |=> (data == $past(ldata))
    );

    // When enabled, not loading, and paused, state holds its value.
    check_pause_holds_state: assert property (
        @(posedge clk) disable iff (!reset_n) (enable && !load && pause) |=> (lfsr_data == $past(lfsr_data))
    );

    // When enabled, not loading, and paused, output holds its value.
    check_pause_holds_output: assert property (
        @(posedge clk) disable iff (!reset_n) (enable && !load && pause) |=> (data == $past(data))
    );

    // When enabled, not loading, and not paused, next state follows LFSR update.
    check_run_updates_state_lfsr: assert property (
        @(posedge clk) disable iff (!reset_n)
            (enable && !load && !pause) |=> (lfsr_data ==
                { $past(lfsr_data[6]),
                  $past(lfsr_data[5]),
                  $past(lfsr_data[4]),
                  $past(lfsr_data[3]) ^ $past(lfsr_data[7]),
                  $past(lfsr_data[2]) ^ $past(lfsr_data[7]),
                  $past(lfsr_data[1]) ^ $past(lfsr_data[7]),
                  $past(lfsr_data[0]),
                  $past(lfsr_data[7]) })
    );

    // When enabled, not loading, and not paused, next output follows LFSR update.
    check_run_updates_output_lfsr: assert property (
        @(posedge clk) disable iff (!reset_n)
            (enable && !load && !pause) |=> (data ==
                { $past(data[6]),
                  $past(data[5]),
                  $past(data[4]),
                  $past(data[3]) ^ $past(data[7]),
                  $past(data[2]) ^ $past(data[7]),
                  $past(data[1]) ^ $past(data[7]),
                  $past(data[0]),
                  $past(data[7]) })
    );

    // Load is ignored when disabled; next state must still be SEED8.
    check_load_ignored_when_disabled: assert property (
        @(posedge clk) disable iff (!reset_n) (!enable && load) |=> (lfsr_data == SEED8)
    );

    // Load has priority over pause when enabled.
    check_load_over_pause_priority: assert property (
        @(posedge clk) disable iff (!reset_n) (enable && load && pause) |=> (lfsr_data == $past(ldata))
    );

endmodule