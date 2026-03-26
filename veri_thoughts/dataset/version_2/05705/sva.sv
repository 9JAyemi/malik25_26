module control_enable_options_sva(
    input logic clk,
    input logic rst_n,
    input logic [7:0] zxuno_addr,
    input logic zxuno_regrd,
    input logic zxuno_regwr,
    input logic [7:0] din,
    input logic [7:0] dout,
    input logic oe_n,
    input logic disable_ay,
    input logic disable_turboay,
    input logic disable_7ffd,
    input logic disable_1ffd,
    input logic disable_romsel7f,
    input logic disable_romsel1f,
    input logic enable_timexmmu,
    input logic disable_spisd,
    input logic disable_timexscr,
    input logic disable_ulaplus,
    input logic disable_radas
);

    localparam [7:0] DEVOPTIONS = 8'h0E;
    localparam [7:0] DEVOPTS2   = 8'h0F;

    // Reset clears all stored control outputs.
    reset_clears_all_control_outputs: assert property (
        @(posedge clk)
        !rst_n |=> (disable_ay == 1'b0) &&
                   (disable_turboay == 1'b0) &&
                   (disable_7ffd == 1'b0) &&
                   (disable_1ffd == 1'b0) &&
                   (disable_romsel7f == 1'b0) &&
                   (disable_romsel1f == 1'b0) &&
                   (enable_timexmmu == 1'b0) &&
                   (disable_spisd == 1'b0) &&
                   (disable_timexscr == 1'b0) &&
                   (disable_ulaplus == 1'b0) &&
                   (disable_radas == 1'b0)
    );

    // Writing DEVOPTIONS updates the mapped outputs on the next cycle.
    write_devoptions_updates_outputs: assert property (
        @(posedge clk) disable iff (!rst_n)
        ((zxuno_regwr == 1'b1) && (zxuno_addr == DEVOPTIONS))
        |=> (disable_ay == $past(din[0])) &&
            (disable_turboay == $past(din[1])) &&
            (disable_7ffd == $past(din[2])) &&
            (disable_1ffd == $past(din[3])) &&
            (disable_romsel7f == $past(din[4])) &&
            (disable_romsel1f == $past(din[5])) &&
            (enable_timexmmu == $past(din[6])) &&
            (disable_spisd == $past(din[7]))
    );

    // Writing DEVOPTS2 updates the mapped outputs on the next cycle.
    write_devopts2_updates_outputs: assert property (
        @(posedge clk) disable iff (!rst_n)
        ((zxuno_regwr == 1'b1) && (zxuno_addr == DEVOPTS2))
        |=> (disable_timexscr == $past(din[0])) &&
            (disable_ulaplus == $past(din[1])) &&
            (disable_radas == $past(din[2]))
    );

    // Writing DEVOPTIONS does not change DEVOPTS2-controlled outputs.
    write_devoptions_preserves_devopts2_outputs: assert property (
        @(posedge clk) disable iff (!rst_n)
        ((zxuno_regwr == 1'b1) && (zxuno_addr == DEVOPTIONS))
        |=> ({disable_radas, disable_ulaplus, disable_timexscr} ==
             $past({disable_radas, disable_ulaplus, disable_timexscr}))
    );

    // Writing DEVOPTS2 does not change DEVOPTIONS-controlled outputs.
    write_devopts2_preserves_devoptions_outputs: assert property (
        @(posedge clk) disable iff (!rst_n)
        ((zxuno_regwr == 1'b1) && (zxuno_addr == DEVOPTS2))
        |=> ({disable_spisd, enable_timexmmu, disable_romsel1f, disable_romsel7f,
              disable_1ffd, disable_7ffd, disable_turboay, disable_ay} ==
             $past({disable_spisd, enable_timexmmu, disable_romsel1f, disable_romsel7f,
                    disable_1ffd, disable_7ffd, disable_turboay, disable_ay}))
    );

    // Without a targeted write, stored control outputs hold their value.
    no_targeted_write_holds_outputs: assert property (
        @(posedge clk) disable iff (!rst_n)
        !((zxuno_regwr == 1'b1) &&
          ((zxuno_addr == DEVOPTIONS) || (zxuno_addr == DEVOPTS2)))
        |=> ({disable_radas, disable_ulaplus, disable_timexscr,
              disable_spisd, enable_timexmmu, disable_romsel1f, disable_romsel7f,
              disable_1ffd, disable_7ffd, disable_turboay, disable_ay} ==
             $past({disable_radas, disable_ulaplus, disable_timexscr,
                    disable_spisd, enable_timexmmu, disable_romsel1f, disable_romsel7f,
                    disable_1ffd, disable_7ffd, disable_turboay, disable_ay}))
    );

    // When no register read is requested, the bus stays deasserted.
    no_read_returns_default_bus: assert property (
        @(posedge clk) disable iff (!rst_n)
        (zxuno_regrd == 1'b0) |-> (oe_n == 1'b1) && (dout == 8'hFF)
    );

    // Reading an unmapped address returns the default bus value.
    read_unknown_address_returns_default_bus: assert property (
        @(posedge clk) disable iff (!rst_n)
        ((zxuno_regrd == 1'b1) &&
         (zxuno_addr != DEVOPTIONS) &&
         (zxuno_addr != DEVOPTS2))
        |-> (oe_n == 1'b1) && (dout == 8'hFF)
    );

    // Reading DEVOPTIONS enables the bus and returns the current bits.
    read_devoptions_returns_current_value: assert property (
        @(posedge clk) disable iff (!rst_n)
        ((zxuno_regrd == 1'b1) && (zxuno_addr == DEVOPTIONS))
        |-> (oe_n == 1'b0) &&
            (dout == {disable_spisd, enable_timexmmu, disable_romsel1f, disable_romsel7f,
                      disable_1ffd, disable_7ffd, disable_turboay, disable_ay})
    );

    // Reading DEVOPTS2 enables the bus and returns the visible low bits.
    read_devopts2_returns_current_low_bits: assert property (
        @(posedge clk) disable iff (!rst_n)
        ((zxuno_regrd == 1'b1) && (zxuno_addr == DEVOPTS2))
        |-> (oe_n == 1'b0) &&
            (dout[2:0] == {disable_radas, disable_ulaplus, disable_timexscr})
    );

    // An immediate DEVOPTS2 read after a write returns the written byte.
    write_then_read_devopts2_returns_written_byte: assert property (
        @(posedge clk) disable iff (!rst_n)
        ((zxuno_regwr == 1'b1) && (zxuno_addr == DEVOPTS2))
        ##1 ((zxuno_regrd == 1'b1) && (zxuno_addr == DEVOPTS2))
        |-> (oe_n == 1'b0) && (dout == $past(din))
    );

endmodule