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
    input logic [5:0]  data_counter,
    input logic        preamble
);

    localparam logic [1:0] IDLE     = 2'b01;
    localparam logic [1:0] ACQUIRE  = 2'b10;

    // Preamble is the AND of the upper three input bits.
    check_preamble_definition: assert property (
        @(posedge mdio_mdc) disable iff (1'b0)
        preamble == (&data_in[31:29])
    );

    // State register loads the previous next_state value.
    check_state_register_update: assert property (
        @(posedge mdio_mdc) disable iff (1'b0)
        1'b1 |=> (current_state == $past(next_state))
    );

    // Data input register shifts in the previous mdio_in_w value.
    check_data_in_shift: assert property (
        @(posedge mdio_mdc) disable iff (1'b0)
        1'b1 |=> (data_in == {$past(data_in[30:0]), $past(mdio_in_w)})
    );

    // Data counter increments on ACQUIRE until the terminal count.
    check_data_counter_increment: assert property (
        @(posedge mdio_mdc) disable iff (1'b0)
        (current_state == ACQUIRE && data_counter != 6'h1f) |=> (data_counter == ($past(data_counter) + 6'd1))
    );

    // Data counter clears on non-ACQUIRE states.
    check_data_counter_clear: assert property (
        @(posedge mdio_mdc) disable iff (1'b0)
        (current_state != ACQUIRE) |=> (data_counter == 6'd0)
    );

    // Data input register holds when not in ACQUIRE.
    check_data_in_hold: assert property (
        @(posedge mdio_mdc) disable iff (1'b0)
        (current_state != ACQUIRE) |=> (data_in == $past(data_in))
    );

    // State machine holds IDLE when the IDLE entry condition is not met.
    check_idle_hold_without_entry: assert property (
        @(posedge mdio_mdc) disable iff (1'b0)
        (current_state == IDLE && !preamble && mdio_in_w) |=> (current_state == IDLE)
    );

    // State machine enters ACQUIRE on the IDLE entry condition.
    check_idle_entry_to_acquire: assert property (
        @(posedge mdio_mdc) disable iff (1'b0)
        (current_state == IDLE && preamble && !mdio_in_w) |=> (current_state == ACQUIRE)
    );

    // State machine holds ACQUIRE until the terminal count.
    check_acquire_hold_until_terminal: assert property (
        @(posedge mdio_mdc) disable iff (1'b0)
        (current_state == ACQUIRE && data_counter != 6'h1f) |=> (current_state == ACQUIRE)
    );

    // State machine clears ACQUIRE on the terminal count.
    check_acquire_terminal_clears_state: assert property (
        @(posedge mdio_mdc) disable iff (1'b0)
        (current_state == ACQUIRE && data_counter == 6'h1f) |=> (current_state == IDLE)
    );

    // Speed select and duplex_mode load from data_in_r on the terminal count.
    check_mdio_load_on_terminal_count: assert property (
        @(posedge mdio_mdc) disable iff (1'b0)
        (current_state == ACQUIRE && data_counter == 6'h1f) |=> (
            speed_select == $past(data_in_r[16:15]) &&
            duplex_mode  == $past(data_in_r[14])
        )
    );

    // Speed select and duplex_mode hold when the terminal count is not reached.
    check_mdio_hold_before_terminal_count: assert property (
        @(posedge mdio_mdc) disable iff (1'b0)
        (current_state == ACQUIRE && data_counter != 6'h1f) |=> (
            speed_select == $past(speed_select) &&
            duplex_mode  == $past(duplex_mode)
        )
    );

    // speed_select and duplex_mode only change after the terminal count.
    check_mdio_change_requires_terminal_count: assert property (
        @(posedge mdio_mdc) disable iff (1'b0)
        (speed_select != $past(speed_select) || duplex_mode != $past(duplex_mode)) |-> ($past(current_state) == ACQUIRE && $past(data_counter) == 6'h1f)
    );

    // speed_select and duplex_mode remain stable outside ACQUIRE.
    check_mdio_hold_outside_acquire: assert property (
        @(posedge mdio_mdc) disable iff (1'b0)
        (current_state != ACQUIRE) |=> (
            speed_select == $past(speed_select) &&
            duplex_mode  == $past(duplex_mode)
        )
    );

    // data_in_r shifts in the previous mdio_in_r value.
    check_data_in_r_shift: assert property (
        @(negedge mdio_mdc) disable iff (1'b0)
        1'b1 |=> (data_in_r == {$past(data_in_r[30:0]), $past(mdio_in_r)})
    );

endmodule