
module digital_clock(
    input clk,
    input reset,
    output [5:0] sec,
    output [5:0] min,
    output [4:0] hr,
    output ampm
);

    // Counters for seconds, minutes, and hours
    reg [5:0] sec_count = 6'b0;
    reg [5:0] min_count = 6'b0;
    reg [4:0] hr_count = 5'b0;

    // Flag to toggle AM/PM
    reg toggle_ampm = 1'b0;

    // Synchronous reset
    always @(posedge clk) begin
        if (reset) begin
            sec_count <= 6'b0;
            min_count <= 6'b0;
            hr_count <= 5'b0;
            toggle_ampm <= 1'b0;
        end else begin
            // Increment second counter every second
            if (sec_count == 6'd49) begin
                sec_count <= 6'b0;
                // Increment minute counter every minute
                if (min_count == 6'd59) begin
                    min_count <= 6'b0;
                    // Increment hour counter every hour
                    if (hr_count == 5'd11 && toggle_ampm == 1'b0) begin
                        hr_count <= 5'b0;
                        toggle_ampm <= 1'b1;
                    end else if (hr_count == 5'd11 && toggle_ampm == 1'b1) begin
                        hr_count <= 5'b0;
                        toggle_ampm <= 1'b0;
                    end else begin
                        hr_count <= hr_count + 5'b1;
                    end
                end else begin
                    min_count <= min_count + 6'b1;
                end
            end else begin
                sec_count <= sec_count + 6'b1;
            end
        end
    end

    // Output values
    assign sec = sec_count;
    assign min = min_count;
    assign ampm = toggle_ampm;
    assign hr = (hr_count == 5'b0) ? 5'd12 :
                (hr_count < 5'd10) ? {4'b0, hr_count} :
                (hr_count < 5'd12) ? hr_count :
                (hr_count == 5'd12) ? 5'b0 :
                (hr_count < 5'd22) ? {4'b0, hr_count - 5'd12} : hr_count - 5'd12;

endmodule
