module traffic_light_sva (
    input logic clk,
    input logic [1:0] current_state,
    input logic pedestrian_button,
    input logic [1:0] next_state
);

    // Green with a pedestrian request transitions to yellow.
    check_green_with_ped_to_yellow: assert property (
        @(posedge clk)
        (current_state == 2'b00 && pedestrian_button) |-> (next_state == 2'b01)
    );

    // Green without a pedestrian request transitions to red.
    check_green_without_ped_to_red: assert property (
        @(posedge clk)
        (current_state == 2'b00 && !pedestrian_button) |-> (next_state == 2'b10)
    );

    // Yellow always transitions to red.
    check_yellow_to_red: assert property (
        @(posedge clk)
        (current_state == 2'b01) |-> (next_state == 2'b10)
    );

    // Red always transitions to green.
    check_red_to_green: assert property (
        @(posedge clk)
        (current_state == 2'b10) |-> (next_state == 2'b00)
    );

    // Invalid state defaults to green.
    check_default_to_green: assert property (
        @(posedge clk)
        (current_state == 2'b11) |-> (next_state == 2'b00)
    );

    // The next state is never the invalid encoding 2'b11.
    check_next_state_never_invalid: assert property (
        @(posedge clk)
        (1'b1) |-> (next_state != 2'b11)
    );

    // Yellow output only occurs from green with a pedestrian request.
    check_yellow_output_source: assert property (
        @(posedge clk)
        (next_state == 2'b01) |-> (current_state == 2'b00 && pedestrian_button)
    );

    // Green output only occurs from red or the default case.
    check_green_output_source: assert property (
        @(posedge clk)
        (next_state == 2'b00) |-> (current_state == 2'b10 || current_state == 2'b11)
    );

    // Red output only occurs from yellow or green without a pedestrian request.
    check_red_output_source: assert property (
        @(posedge clk)
        (next_state == 2'b10) |-> (current_state == 2'b01 || (current_state == 2'b00 && !pedestrian_button))
    );

endmodule