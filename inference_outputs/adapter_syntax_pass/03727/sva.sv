module mdc_mdio_sva (
    input logic        mdio_mdc,
    input logic        mdio_in_w,
    input logic        mdio_in_r,
    input logic [1:0]  speed_select,
    input logic        duplex_mode,
    input logic [1:0]  current_state,
    input logic [1:0]  next_state,
    input logic [31:0] data_in,
    input logic [31:0] data_in_r,
    input logic [5:0]  data_counter
);

    localparam logic [1:0] IDLE     = 2'b01;
    localparam logic [1:0] ACQUIRE  = 2'b10;

    // IDLE holds when the preamble is not detected.
    check_idle_holds_without_preamble: assert property (
        @(posedge mdio_mdc)
        (current_state == IDLE) && !(&data_in) |=> (current_state == IDLE)
    );

    // IDLE advances to ACQUIRE on the first valid preamble sample.
    check_idle_to_acquire_on_preamble: assert property (
        @(posedge mdio_mdc)
        (current_state == IDLE) && (&data_in) && (mdio_in_w == 1'b0) |=> (current_state == ACQUIRE)
    );

    // ACQUIRE holds until the final data sample is reached.
    check_acquire_holds_until_final_sample: assert property (
        @(posedge mdio_mdc)
        (current_state == ACQUIRE) && (data_counter != 6'h1f) |=> (current_state == ACQUIRE)
    );

    // ACQUIRE returns to IDLE on the final data sample.
    check_acquire_to_idle_on_final_sample: assert property (
        @(posedge mdio_mdc)
        (current_state == ACQUIRE) && (data_counter == 6'h1f) |=> (current_state == IDLE)
    );

    // next_state matches the IDLE decode when current_state is IDLE.
    check_next_state_decode_idle: assert property (
        @(posedge mdio_mdc)
        (current_state == IDLE) |-> (next_state == IDLE)
    );

    // next_state matches the ACQUIRE decode when current_state is ACQUIRE.
    check_next_state_decode_acquire: assert property (
        @(posedge mdio_mdc)
        (current_state == ACQUIRE) |-> (next_state == ACQUIRE)
    );

    // next_state is always one of the defined encodings.
    check_next_state_legal_values: assert property (
        @(posedge mdio_mdc)
        (next_state inside {IDLE, ACQUIRE})
    );

    // data_in shifts in the previous mdio_in_w value on each rising edge.
    check_data_in_shift: assert property (
        @(posedge mdio_mdc)
        1'b1 |=> (data_in == {$past(data_in[30:0]), $past(mdio_in_w)})
    );

    // data_counter increments by one on each rising edge while in ACQUIRE.
    check_data_counter_increment_in_acquire: assert property (
        @(posedge mdio_mdc)
        (current_state == ACQUIRE) |=> (data_counter == ($past(data_counter) + 6'd1))
    );

    // data_counter clears to zero on each rising edge outside ACQUIRE.
    check_data_counter_clear_outside_acquire: assert property (
        @(posedge mdio_mdc)
        (current_state != ACQUIRE) |=> (data_counter == 6'd0)
    );

    // data_in_r shifts in the previous mdio_in_r value on each falling edge.
    check_data_in_r_shift: assert property (
        @(negedge mdio_mdc)
        1'b1 |=> (data_in_r == {$past(data_in_r[30:0]), $past(mdio_in_r)})
    );

    // speed_select is loaded from data_in_r[16:15] on the final data sample.
    check_speed_select_load_on_final_sample: assert property (
        @(posedge mdio_mdc)
        (current_state == IDLE) && (data_counter == 6'h1f) &&
        (&data_in) && (data_in[31] == 1'b0) && (data_in[29:28] == 2'b10) &&
        (data_in[27:23] == 5'h10) && (data_in[22:18] == 5'h11)
        |=> (speed_select == $past(data_in_r[16:15]))
    );

    // duplex_mode is loaded from data_in_r[14] on the final data sample.
    check_duplex_mode_load_on_final_sample: assert property (
        @(posedge mdio_mdc)
        (current_state == IDLE) && (data_counter == 6'h1f) &&
        (&data_in) && (data_in[31] == 1'b0) && (data_in[29:28] == 2'b10) &&
        (data_in[27:23] == 5'h10) && (data_in[22:18] == 5'h11)
        |=> (duplex_mode == $past(data_in_r[14]))
    );

    // speed_select and duplex_mode hold when no final data sample is detected.
    check_mdio_mode_hold_without_final_sample: assert property (
        @(posedge mdio_mdc)
        (current_state == IDLE) && (data_counter != 6'h1f) |=> (speed_select == $past(speed_select)) &&
                                                              (duplex_mode == $past(duplex_mode))
    );

endmodule