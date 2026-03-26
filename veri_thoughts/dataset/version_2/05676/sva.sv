module dcf77_validy_checker_sva (
    input logic        clk,
    input logic        reset,
    input logic [58:0] dcf_bits,
    input logic        dcf_new_sec,
    input logic        signal_valid
);

    wire parity_min;
    wire parity_hour;
    wire parity_date;

    assign parity_min  = (^dcf_bits[27:21] == dcf_bits[28]);
    assign parity_hour = (^dcf_bits[34:29] == dcf_bits[35]);
    assign parity_date = (^dcf_bits[57:36] == dcf_bits[58]);

    // signal_valid must match the RTL combinational equation.
    check_signal_valid_definition: assert property (
        @(posedge clk) disable iff (reset)
        signal_valid == (parity_min && parity_hour && parity_date &&
                         (dcf_bits[0] == 1'b0) && (dcf_bits[20] == 1'b1) && dcf_new_sec)
    );

    // signal_valid can only assert with correct minute parity.
    check_valid_requires_minute_parity: assert property (
        @(posedge clk) disable iff (reset)
        signal_valid |-> parity_min
    );

    // signal_valid can only assert with correct hour parity.
    check_valid_requires_hour_parity: assert property (
        @(posedge clk) disable iff (reset)
        signal_valid |-> parity_hour
    );

    // signal_valid can only assert with correct date parity.
    check_valid_requires_date_parity: assert property (
        @(posedge clk) disable iff (reset)
        signal_valid |-> parity_date
    );

    // signal_valid can only assert when bit 0 is zero.
    check_valid_requires_bit0_zero: assert property (
        @(posedge clk) disable iff (reset)
        signal_valid |-> (dcf_bits[0] == 1'b0)
    );

    // signal_valid can only assert when bit 20 is one.
    check_valid_requires_bit20_one: assert property (
        @(posedge clk) disable iff (reset)
        signal_valid |-> (dcf_bits[20] == 1'b1)
    );

    // signal_valid can only assert on a new second.
    check_valid_requires_new_second: assert property (
        @(posedge clk) disable iff (reset)
        signal_valid |-> dcf_new_sec
    );

    // All required checks passing must assert signal_valid.
    check_all_conditions_imply_valid: assert property (
        @(posedge clk) disable iff (reset)
        (parity_min && parity_hour && parity_date &&
         (dcf_bits[0] == 1'b0) && (dcf_bits[20] == 1'b1) && dcf_new_sec) |-> signal_valid
    );

endmodule