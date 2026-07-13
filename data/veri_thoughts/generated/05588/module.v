
module assert_time_assert (
    input clk,
    input reset_n,
    input start_event,
    input test_expr,
    input [31:0] window,
    input ignore_new_start,
    input reset_on_new_start,
    input error_on_new_start,
    input xzcheck_enable,
    output reg assertion
);

    parameter num_cks = 1000; // Default value for number of clock cycles

    reg [31:0] timer;
    reg active;
    reg [31:0] num_cks_counter;

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            timer <= 0;
            active <= 0;
            assertion <= 0;
        end else begin
            num_cks_counter <= num_cks_counter + 1;
            if (num_cks_counter == num_cks) begin
                num_cks_counter <= 0;
                if (start_event) begin
                    timer <= 0;
                    active <= 1;
                end
                if (active) begin
                    timer <= timer + 1;
                    if (timer >= window) begin
                        assertion <= test_expr;
                        active <= 0;
                    end
                    if (start_event && !ignore_new_start) begin
                        if (reset_on_new_start) begin
                            assertion <= 0;
                        end
                        if (error_on_new_start) begin
                            assertion <= 0;
                        end
                        active <= 1;
                        timer <= 0;
                    end
                end
            end
        end
    end

endmodule