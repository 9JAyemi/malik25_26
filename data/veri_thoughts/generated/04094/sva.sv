module ddr3_int_ex_lfsr8_sva #(
    parameter logic [31:0] seed = 32
) (
    input logic       clk,
    input logic       reset_n,
    input logic       enable,
    input logic       pause,
    input logic       load,
    input logic [7:0] data,
    input logic [7:0] ldata
);

    localparam logic [7:0] SEED8 = seed[7:0];

    // Active-low reset forces the output to the seed value.
    check_reset_forces_seed: assert property (
        @(posedge clk) !reset_n |-> (data == SEED8)
    );

    // When enable is low, the next state reloads the seed regardless of load or pause.
    check_disable_reloads_seed: assert property (
        @(posedge clk) disable iff (!reset_n)
        (!enable) |=> (data == SEED8)
    );

    // When enabled with load asserted, the next state becomes the load data.
    check_load_updates_state: assert property (
        @(posedge clk) disable iff (!reset_n)
        (enable && load) |=> (data == $past(ldata))
    );

    // When paused without load, the state holds its current value.
    check_pause_holds_state: assert property (
        @(posedge clk) disable iff (!reset_n)
        (enable && !load && pause) |=> (data == $past(data))
    );

    // When enabled and not paused or loaded, the LFSR advances with the implemented tap mapping.
    check_lfsr_advance: assert property (
        @(posedge clk) disable iff (!reset_n)
        (enable && !load && !pause) |=> (
            data == {
                $past(data[6]),
                $past(data[5]),
                $past(data[4]),
                $past(data[3]) ^ $past(data[7]),
                $past(data[2]) ^ $past(data[7]),
                $past(data[1]) ^ $past(data[7]),
                $past(data[0]),
                $past(data[7])
            }
        )
    );

endmodule