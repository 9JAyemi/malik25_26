
module debounce(
    input clk,
    input button,
    output reg button_state,
    output reg button_up,
    output reg button_down
);

    // Register to hold the current state of the button
    reg current_state;

    // Register to hold the previous state of the button
    reg previous_state;

    // Debounce counter
    reg [15:0] debounce_counter;

    // Define the initial values of the registers
    initial begin
        current_state = 1'b0;
        previous_state = 1'b0;
        debounce_counter = 16'd0;
        button_state = 1'b0;
        button_up = 1'b0;
        button_down = 1'b0;
    end

    // Debounce logic
    always @(posedge clk) begin
        // Update the current state of the button
        current_state <= button;

        // Increment the debounce counter
        if (debounce_counter < 16'd10000) begin
            debounce_counter <= debounce_counter + 16'd1;
        end

        // Check if the button has been pressed for long enough
        if (debounce_counter == 16'd10000) begin
            // Update the button state
            button_state <= current_state;
            if (current_state & ~previous_state) begin
                button_down <= 1;
            end else if (~current_state & previous_state) begin
                button_up <= 1;
            end
        end

        // Update the previous state of the button
        previous_state <= current_state;
    end

endmodule
