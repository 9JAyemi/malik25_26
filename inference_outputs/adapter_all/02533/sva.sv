module Mux_3x1_bv2_sva #(parameter W=32) (
    input logic [1:0] select,
    input logic [W-1:0] ch_0,
    input logic [W-1:0] ch_1,
    input logic [W-1:0] ch_2,
    input logic [W-1:0] data_out
);

    // Select 00 drives zero.
    check_select_00_drives_zero: assert property (
        @($global_clock) (select == 2'b00) |-> (data_out == {W{1'b0}})
    );

    // Select 01 drives ch_0.
    check_select_01_drives_ch0: assert property (
        @($global_clock) (select == 2'b01) |-> (data_out == ch_0)
    );

    // Select 10 drives ch_1.
    check_select_10_drives_ch1: assert property (
        @($global_clock) (select == 2'b10) |-> (data_out == ch_1)
    );

    // Select 11 drives ch_2.
    check_select_11_drives_ch2: assert property (
        @($global_clock) (select == 2'b11) |-> (data_out == ch_2)
    );

    // With select 01 held and ch_0 stable, data_out stays stable.
    check_select_01_stable_when_ch0_stable: assert property (
        @($global_clock) (select == 2'b01 && $stable(select) && $stable(ch_0)) |-> $stable(data_out)
    );

    // With select 10 held and ch_1 stable, data_out stays stable.
    check_select_10_stable_when_ch1_stable: assert property (
        @($global_clock) (select == 2'b10 && $stable(select) && $stable(ch_1)) |-> $stable(data_out)
    );

    // With select 11 held and ch_2 stable, data_out stays stable.
    check_select_11_stable_when_ch2_stable: assert property (
        @($global_clock) (select == 2'b11 && $stable(select) && $stable(ch_2)) |-> $stable(data_out)
    );

    // With select 01 held and ch_0 changing, data_out changes.
    check_select_01_tracks_ch0: assert property (
        @($global_clock) (select == 2'b01 && $stable(select) && $changed(ch_0)) |-> $changed(data_out)
    );

    // With select 10 held and ch_1 changing, data_out changes.
    check_select_10_tracks_ch1: assert property (
        @($global_clock) (select == 2'b10 && $stable(select) && $changed(ch_1)) |-> $changed(data_out)
    );

    // With select 11 held and ch_2 changing, data_out changes.
    check_select_11_tracks_ch2: assert property (
        @($global_clock) (select == 2'b11 && $stable(select) && $changed(ch_2)) |-> $changed(data_out)
    );

endmodule