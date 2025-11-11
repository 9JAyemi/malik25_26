module assert_unchange_assert #(
    parameter width = 8
) (
    input clk, reset_n, start_event, xzcheck_enable,
    input [width-1:0] test_expr,
    input window, ignore_new_start, reset_on_new_start, error_on_new_start,
    output reg pass, fail, error
);

    parameter num_cks = 2;

    reg [width-1:0] prev_test_expr;
    reg [num_cks-1:0] window_counter;
    reg start_detected;
    reg reset_detected;

    always @(posedge clk) begin
        if (!reset_n) begin
            prev_test_expr <= 'bx;
            window_counter <= 0;
            start_detected <= 0;
            reset_detected <= 0;
            pass <= 0;
            fail <= 0;
            error <= 0;
        end else begin
            if (reset_detected) begin
                prev_test_expr <= 'bx;
                window_counter <= 0;
                start_detected <= 0;
                reset_detected <= 0;
                pass <= 0;
                fail <= 0;
                error <= 0;
            end else begin
                if (start_event && !start_detected) begin
                    prev_test_expr <= test_expr;
                    window_counter <= 1;
                    start_detected <= 1;
                    reset_detected <= 0;
                    pass <= 0;
                    fail <= 0;
                    error <= 0;
                end else if (start_event && reset_on_new_start) begin
                    prev_test_expr <= test_expr;
                    window_counter <= 1;
                    start_detected <= 1;
                    reset_detected <= 0;
                    pass <= 0;
                    fail <= 0;
                    error <= error_on_new_start;
                end else if (start_event && error_on_new_start) begin
                    prev_test_expr <= 'bx;
                    window_counter <= 0;
                    start_detected <= 0;
                    reset_detected <= 0;
                    pass <= 0;
                    fail <= 0;
                    error <= 1;
                end else if (start_detected && window_counter < window) begin
                    if (test_expr !== prev_test_expr && xzcheck_enable) begin
                        fail <= 1;
                        error <= 1;
                    end else begin
                        fail <= 0;
                        error <= 0;
                    end
                    prev_test_expr <= test_expr;
                    window_counter <= window_counter + 1;
                    pass <= 0;
                end else if (start_detected && window_counter == window) begin
                    if (test_expr !== prev_test_expr && xzcheck_enable) begin
                        fail <= 1;
                        error <= 1;
                    end else begin
                        fail <= 0;
                        error <= 0;
                    end
                    prev_test_expr <= test_expr;
                    window_counter <= 0;
                    start_detected <= ignore_new_start;
                    reset_detected <= 0;
                    pass <= 1;
                end else if (start_detected && ignore_new_start) begin
                    if (test_expr !== prev_test_expr && xzcheck_enable) begin
                        fail <= 1;
                        error <= 1;
                    end else begin
                        fail <= 0;
                        error <= 0;
                    end
                    prev_test_expr <= test_expr;
                    window_counter <= window_counter + 1;
                    pass <= 0;
                end else if (start_detected && reset_on_new_start) begin
                    prev_test_expr <= test_expr;
                    window_counter <= 1;
                    start_detected <= 1;
                    reset_detected <= 1;
                    pass <= 0;
                    fail <= 0;
                    error <= 0;
                end else if (start_detected && error_on_new_start) begin
                    prev_test_expr <= 'bx;
                    window_counter <= 0;
                    start_detected <= 0;
                    reset_detected <= 0;
                    pass <= 0;
                    fail <= 0;
                    error <= 1;
                end
            end
        end
    end

endmodule