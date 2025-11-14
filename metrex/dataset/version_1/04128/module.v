module VGACtrl(
    input clk,
    input reset,
    output reg vga_h_sync,
    output reg vga_v_sync,
    output reg inDisplayArea,
    output reg [9:0] CounterX,
    output reg [9:0] CounterY
);

    // Constants for VGA timing
    parameter H_SYNC_PERIOD = 96;
    parameter H_SYNC_PULSE_WIDTH = 16;
    parameter V_SYNC_PERIOD = 8000;
    parameter V_SYNC_PULSE_WIDTH = 2;
    parameter DISPLAY_WIDTH = 640;
    parameter DISPLAY_HEIGHT = 480;

    // Internal signals
    reg [9:0] h_counter;
    reg [9:0] v_counter;

    always @(posedge clk, posedge reset) begin
        if (reset) begin
            // Reset counters and signals
            h_counter <= 0;
            v_counter <= 0;
            vga_h_sync <= 0;
            vga_v_sync <= 0;
            inDisplayArea <= 0;
            CounterX <= 0;
            CounterY <= 0;
        end else begin
            // Update horizontal counter
            if (h_counter == DISPLAY_WIDTH - 1) begin
                h_counter <= 0;
                CounterX <= h_counter;
            end else begin
                h_counter <= h_counter + 1;
                CounterX <= h_counter;
            end

            // Update vertical counter
            if (v_counter == DISPLAY_HEIGHT - 1) begin
                v_counter <= 0;
                CounterY <= v_counter;
            end else begin
                v_counter <= v_counter + 1;
                CounterY <= v_counter;
            end

            // Update sync signals
            if (h_counter >= DISPLAY_WIDTH - H_SYNC_PULSE_WIDTH) begin
                vga_h_sync <= 1;
            end else begin
                vga_h_sync <= 0;
            end

            if (v_counter >= DISPLAY_HEIGHT - V_SYNC_PULSE_WIDTH) begin
                vga_v_sync <= 1;
            end else begin
                vga_v_sync <= 0;
            end

            // Update display area signal
            if (h_counter < DISPLAY_WIDTH && v_counter < DISPLAY_HEIGHT) begin
                inDisplayArea <= 1;
            end else begin
                inDisplayArea <= 0;
            end
        end
    end

endmodule