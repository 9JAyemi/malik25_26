module speaker_sva (
    input logic clk,
    input logic rst,
    input logic [7:0] wb_dat_i,
    input logic [7:0] wb_dat_o,
    input logic wb_we_i,
    input logic wb_stb_i,
    input logic wb_cyc_i,
    input logic wb_ack_o,
    input logic timer2,
    input logic speaker_
);
    // wb_ack_o equals wb_stb_i AND wb_cyc_i each cycle.
    check_wb_ack_definition: assert property (
        @(posedge clk) disable iff (rst) wb_ack_o == (wb_stb_i && wb_cyc_i)
    );

    // If wb_stb_i and wb_cyc_i are stable, wb_ack_o is stable.
    check_wb_ack_stability_if_inputs_stable: assert property (
        @(posedge clk) disable iff (rst) ($stable(wb_stb_i) && $stable(wb_cyc_i)) |-> $stable(wb_ack_o)
    );

    // A write request implies wb_ack_o is HIGH in the same cycle.
    check_write_implies_ack: assert property (
        @(posedge clk) disable iff (rst) (wb_stb_i && wb_cyc_i && wb_we_i) |-> (wb_ack_o == 1'b1)
    );

    // speaker_ equals timer2 AND wb_dat_o[1] each cycle.
    check_speaker_definition: assert property (
        @(posedge clk) disable iff (rst) speaker_ == (timer2 & wb_dat_o[1])
    );

    // If timer2 and wb_dat_o[1] are stable, speaker_ is stable.
    check_speaker_stability_if_inputs_stable: assert property (
        @(posedge clk) disable iff (rst) ($stable(timer2) && $stable(wb_dat_o[1])) |-> $stable(speaker_)
    );

    // Reset drives wb_dat_o to 0x00 on the next cycle (synchronous reset).
    check_reset_clears_data_next: assert property (
        @(posedge clk) rst |=> (wb_dat_o == 8'h00)
    );

    // When not in reset, a write updates wb_dat_o with wb_dat_i on the next cycle.
    check_write_updates_data_next: assert property (
        @(posedge clk) disable iff (rst) (wb_stb_i && wb_cyc_i && wb_we_i) |=> (wb_dat_o == $past(wb_dat_i))
    );

    // When not in reset and no write, wb_dat_o holds its value on the next cycle.
    check_hold_without_write: assert property (
        @(posedge clk) disable iff (rst) !(wb_stb_i && wb_cyc_i && wb_we_i) |=> (wb_dat_o == $past(wb_dat_o))
    );

    // wb_dat_o can change only due to reset or a write in the previous cycle.
    check_data_changes_only_on_write_or_reset: assert property (
        @(posedge clk) disable iff (rst) $changed(wb_dat_o) |-> ($past(rst) || $past(wb_stb_i && wb_cyc_i && wb_we_i))
    );

    // While reset is held across cycles, wb_dat_o remains 0x00.
    check_data_zero_when_reset_held: assert property (
        @(posedge clk) (rst && $past(rst)) |-> (wb_dat_o == 8'h00)
    );
endmodule