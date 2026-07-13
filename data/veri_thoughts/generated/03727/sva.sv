module mdc_mdio_sva #(
    parameter [4:0] PHY_AD = 5'b10000
) (
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

    localparam [1:0] IDLE    = 2'b01;
    localparam [1:0] ACQUIRE = 2'b10;

    // IDLE with a full preamble and low write bit selects ACQUIRE.
    check_idle_start_selects_acquire: assert property (
        @(posedge mdio_mdc)
        (current_state == IDLE && (&data_in) && (mdio_in_w == 1'b0)) |-> (next_state == ACQUIRE)
    );

    // IDLE without the start condition keeps next_state in IDLE.
    check_idle_non_start_stays_idle: assert property (
        @(posedge mdio_mdc)
        (current_state == IDLE && !((&data_in) && (mdio_in_w == 1'b0))) |-> (next_state == IDLE)
    );

    // ACQUIRE stays active before the terminal count.
    check_acquire_before_last_stays_acquire: assert property (
        @(posedge mdio_mdc)
        (current_state == ACQUIRE && data_counter != 6'h1f) |-> (next_state == ACQUIRE)
    );

    // ACQUIRE returns to IDLE at the terminal count.
    check_acquire_last_returns_idle: assert property (
        @(posedge mdio_mdc)
        (current_state == ACQUIRE && data_counter == 6'h1f) |-> (next_state == IDLE)
    );

    // The state register loads next_state on each rising edge.
    check_state_register_loads_next_state: assert property (
        @(posedge mdio_mdc)
        1'b1 |=> (current_state == $past(next_state))
    );

    // data_in shifts in mdio_in_w on each rising edge.
    check_data_in_shifts_write_bit: assert property (
        @(posedge mdio_mdc)
        1'b1 |=> ((data_in[31:1] == $past(data_in[30:0])) &&
                  (data_in[0]    == $past(mdio_in_w)))
    );

    // data_in_r shifts in mdio_in_r on each falling edge.
    check_data_in_r_shifts_read_bit: assert property (
        @(negedge mdio_mdc)
        1'b1 |=> ((data_in_r[31:1] == $past(data_in_r[30:0])) &&
                  (data_in_r[0]    == $past(mdio_in_r)))
    );

    // data_counter increments while ACQUIRE is active.
    check_counter_increments_in_acquire: assert property (
        @(posedge mdio_mdc)
        (current_state == ACQUIRE) |=> (data_counter == ($past(data_counter) + 6'h1))
    );

    // data_counter clears when not in ACQUIRE.
    check_counter_clears_outside_acquire: assert property (
        @(posedge mdio_mdc)
        (current_state != ACQUIRE) |=> (data_counter == 6'h0)
    );

    // A matching decoded frame updates speed_select and duplex_mode.
    check_outputs_update_on_match: assert property (
        @(posedge mdio_mdc)
        ((data_counter == 6'h1f) &&
         (data_in[31]    == 1'b0) &&
         (data_in[29:28] == 2'b10) &&
         (data_in[27:23] == PHY_AD) &&
         (data_in[22:18] == 5'h11)) |=> 
        ((speed_select == $past(data_in_r[16:15])) &&
         (duplex_mode  == $past(data_in_r[14])))
    );

    // Without a matching decoded frame, the outputs hold their values.
    check_outputs_hold_without_match: assert property (
        @(posedge mdio_mdc)
        !((data_counter == 6'h1f) &&
          (data_in[31]    == 1'b0) &&
          (data_in[29:28] == 2'b10) &&
          (data_in[27:23] == PHY_AD) &&
          (data_in[22:18] == 5'h11)) |=> 
        ((speed_select == $past(speed_select)) &&
         (duplex_mode  == $past(duplex_mode)))
    );

endmodule