module mdc_mdio_sva (
    input logic        mdio_mdc,
    input logic        mdio_in_w,
    input logic        mdio_in_r,
    input logic [1:0]  speed_select,
    input logic        duplex_mode
);

// IDLE on the rising edge advances to ACQUIRE when the preamble is detected.
    check_idle_to_acquire_on_preamble: assert property (
        @(posedge mdio_mdc) (current_state == IDLE && preamble && !mdio_in_w) |=> (current_state == ACQUIRE)
    );

// IDLE on the rising edge stays IDLE when the preamble is not detected.
    check_idle_stays_idle_no_preamble: assert property (
        @(posedge mdio_mdc) (current_state == IDLE && !preamble) |=> (current_state == IDLE)
    );

// IDLE on the rising edge stays IDLE when mdio_in_w is HIGH.
    check_idle_stays_idle_w_high: assert property (
        @(posedge mdio_mdc) (current_state == IDLE && mdio_in_w) |=> (current_state == IDLE)
    );

// ACQUIRE on the rising edge advances to IDLE when the 32-bit window is complete.
    check_acquire_to_idle_on_window_complete: assert property (
        @(posedge mdio_mdc) (current_state == ACQUIRE && data_counter == 6'h1f) |=> (current_state == IDLE)
    );

// ACQUIRE on the rising edge stays ACQUIRE when the 32-bit window is not complete.
    check_acquire_stays_acquire_on_window_incomplete: assert property (
        @(posedge mdio_mdc) (current_state == ACQUIRE && data_counter != 6'h1f) |=> (current_state == ACQUIRE)
    );

// ACQUIRE on the rising edge increments data_counter when not at 31.
    check_acquire_increments_counter: assert property (
        @(posedge mdio_mdc) (current_state == ACQUIRE && data_counter != 6'h1f) |=> (data_counter == ($past(data_counter) + 6'd1))
    );

// ACQUIRE on the rising edge clears data_counter when at 31.
    check_acquire_clears_counter_at_max: assert property (
        @(posedge mdio_mdc) (current_state == ACQUIRE && data_counter == 6'h1f) |=> (data_counter == 6'd0)
    );

// ACQUIRE on the rising edge updates speed_select and duplex_mode on a match.
    check_acquire_updates_mdio_on_match: assert property (
        @(posedge mdio_mdc) (current_state == ACQUIRE && data_counter == 6'h1f &&
                             data_in[31] == 1'b0 && data_in[29:28] == 2'b10 &&
                             data_in[27:23] == PHY_AD && data_in[22:18] == 5'h11) |=> (
            speed_select == data_in_r[16:15] &&
            duplex_mode == data_in_r[14]
        )
    );

// ACQUIRE on the rising edge holds speed_select and duplex_mode when no match.
    check_acquire_holds_mdio_on_no_match: assert property (
        @(posedge mdio_mdc) (current_state == ACQUIRE && data_counter == 6'h1f &&
                             !(data_in[31] == 1'b0 && data_in[29:28] == 2'b10 &&
                               data_in[27:23] == PHY_AD && data_in[22:18] == 5'h11)) |=> (
            speed_select == $past(speed_select) &&
            duplex_mode == $past(duplex_mode)
        )
    );

// Rising edges on mdio_in_w and mdio_in_r are captured into data_in and data_in_r.
    check_capture_inputs_on_rising_edges: assert property (
        @(posedge mdio_mdc) 1'b1 |=> (
            data_in[31:1] == $past(data_in[30:0]) &&
            data_in[0] == mdio_in_w &&
            data_in_r[31:1] == $past(data_in_r[30:0]) &&
            data_in_r[0] == mdio_in_r
        )
    );

endmodule
