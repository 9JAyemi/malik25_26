module keypressed_sva (
    input logic       clock,
    input logic       reset,
    input logic       enable_in,
    input logic       enable_out,
    input logic [1:0] key_state,
    input logic [1:0] next_key_state
);

    localparam [1:0] KEY_FREE     = 2'b00;
    localparam [1:0] KEY_PRESSED  = 2'b01;
    localparam [1:0] KEY_RELEASED = 2'b10;

    // Reset drives the state to KEY_FREE.
    check_reset_state: assert property (
        @(posedge clock) !reset |-> (key_state == KEY_FREE)
    );

    // Reset keeps the output low.
    check_reset_output: assert property (
        @(posedge clock) !reset |-> (enable_out == 1'b0)
    );

    // KEY_FREE with a low input decodes to KEY_PRESSED.
    check_next_free_to_pressed: assert property (
        @(posedge clock) disable iff (!reset)
        (key_state == KEY_FREE && enable_in == 1'b0) |-> (next_key_state == KEY_PRESSED)
    );

    // KEY_FREE with a high input stays in KEY_FREE.
    check_next_free_stays_free: assert property (
        @(posedge clock) disable iff (!reset)
        (key_state == KEY_FREE && enable_in == 1'b1) |-> (next_key_state == KEY_FREE)
    );

    // KEY_PRESSED with a low input stays in KEY_PRESSED.
    check_next_pressed_stays_pressed: assert property (
        @(posedge clock) disable iff (!reset)
        (key_state == KEY_PRESSED && enable_in == 1'b0) |-> (next_key_state == KEY_PRESSED)
    );

    // KEY_PRESSED with a high input decodes to KEY_RELEASED.
    check_next_pressed_to_released: assert property (
        @(posedge clock) disable iff (!reset)
        (key_state == KEY_PRESSED && enable_in == 1'b1) |-> (next_key_state == KEY_RELEASED)
    );

    // KEY_RELEASED always decodes back to KEY_FREE.
    check_next_released_to_free: assert property (
        @(posedge clock) disable iff (!reset)
        (key_state == KEY_RELEASED) |-> (next_key_state == KEY_FREE)
    );

    // KEY_FREE advances to KEY_PRESSED when the input is low.
    check_state_free_to_pressed: assert property (
        @(posedge clock) disable iff (!reset)
        (key_state == KEY_FREE && enable_in == 1'b0) |=> (key_state == KEY_PRESSED)
    );

    // KEY_FREE stays in KEY_FREE when the input is high.
    check_state_free_stays_free: assert property (
        @(posedge clock) disable iff (!reset)
        (key_state == KEY_FREE && enable_in == 1'b1) |=> (key_state == KEY_FREE)
    );

    // KEY_PRESSED stays in KEY_PRESSED while the input remains low.
    check_state_pressed_stays_pressed: assert property (
        @(posedge clock) disable iff (!reset)
        (key_state == KEY_PRESSED && enable_in == 1'b0) |=> (key_state == KEY_PRESSED)
    );

    // KEY_PRESSED advances to KEY_RELEASED when the input goes high.
    check_state_pressed_to_released: assert property (
        @(posedge clock) disable iff (!reset)
        (key_state == KEY_PRESSED && enable_in == 1'b1) |=> (key_state == KEY_RELEASED)
    );

    // KEY_RELEASED always returns to KEY_FREE on the next cycle.
    check_state_released_to_free: assert property (
        @(posedge clock) disable iff (!reset)
        (key_state == KEY_RELEASED) |=> (key_state == KEY_FREE)
    );

    // The output is low in KEY_FREE.
    check_output_low_in_free: assert property (
        @(posedge clock) disable iff (!reset)
        (key_state == KEY_FREE) |-> (enable_out == 1'b0)
    );

    // The output is low in KEY_PRESSED.
    check_output_low_in_pressed: assert property (
        @(posedge clock) disable iff (!reset)
        (key_state == KEY_PRESSED) |-> (enable_out == 1'b0)
    );

    // The output is high in KEY_RELEASED.
    check_output_high_in_released: assert property (
        @(posedge clock) disable iff (!reset)
        (key_state == KEY_RELEASED) |-> (enable_out == 1'b1)
    );

endmodule