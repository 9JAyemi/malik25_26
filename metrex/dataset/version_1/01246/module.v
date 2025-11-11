module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input [7:0] d,    // Input data for the adder
    output pwm,       // PWM output
    output reg [7:0] q,   // 8-bit output from the counter
    output reg [7:0] out  // Final output from the functional module
);

    reg [7:0] counter;
    reg [7:0] adder_out;
    reg pwm_out;

    // Counter module
    always @(posedge clk) begin
        if (reset) begin
            counter <= 8'b0;
        end else begin
            if (counter == 8'hff) begin
                counter <= 8'b0;
            end else begin
                counter <= counter + 1;
            end
        end
    end

    // Adder module
    always @(posedge clk) begin
        adder_out <= counter + d;
    end

    // PWM module
    always @(posedge clk) begin
        if (adder_out > 8'h80) begin
            pwm_out <= 1'b1;
        end else begin
            pwm_out <= 1'b0;
        end
    end

    // Functional module
    always @(posedge clk) begin
        q <= counter;
        out <= q * pwm_out;
    end

    // Output assignments
    assign pwm = pwm_out;

endmodule