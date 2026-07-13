module contador_AD_MM_2dig_sva (
    input logic clk,
    input logic reset,
    input logic [3:0] en_count,
    input logic enUP,
    input logic enDOWN,
    input logic [7:0] data_MM
);

    // Helper: decode 2-digit BCD to integer
    function automatic int unsigned bcd8_to_int (input logic [7:0] bcd);
        return int'(bcd[7:4]) * 10 + int'(bcd[3:0]);
    endfunction

    // Helper: increment modulo 60
    function automatic int unsigned inc_mod60 (input int unsigned v);
        return (v >= 59) ? 0 : (v + 1);
    endfunction

    // Helper: decrement modulo 60
    function automatic int unsigned dec_mod60 (input int unsigned v);
        return (v == 0) ? 59 : (v - 1);
    endfunction

    // Helper: data_MM is valid BCD in range 00..59
    function automatic bit is_valid_bcd_00_59 (input logic [7:0] b);
        return (b[7:4] <= 4'd5) && (b[3:0] <= 4'd9);
    endfunction

    ///// Reset behavior /////
    // While reset is asserted HIGH, the displayed value is 00.
    reset_drives_zero: assert property (
        @(posedge clk) reset |-> (data_MM == 8'h00)
    );

    ///// Output encoding rules /////
    // data_MM is always a valid 2-digit BCD value in the range 00..59.
    bcd_range_valid: assert property (
        @(posedge clk) disable iff (reset) is_valid_bcd_00_59(data_MM)
    );

    ///// Hold behavior /////
    // When en_count != 2, the value holds (no change next cycle).
    hold_when_count_disabled: assert property (
        @(posedge clk) disable iff (reset)
            (en_count != 4'd2) |=> (data_MM == $past(data_MM))
    );

    // When enabled (en_count==2) but no direction requested, the value holds.
    hold_when_no_dir_enabled: assert property (
        @(posedge clk) disable iff (reset)
            (en_count == 4'd2) && !enUP && !enDOWN |=> (data_MM == $past(data_MM))
    );

    ///// Up-count behavior /////
    // When enabled and enUP is HIGH (regardless of enDOWN), increment modulo 60.
    inc_on_up_enabled: assert property (
        @(posedge clk) disable iff (reset)
            (en_count == 4'd2) && enUP
            |=> (bcd8_to_int(data_MM) == inc_mod60(bcd8_to_int($past(data_MM))))
    );

    // When both enUP and enDOWN are HIGH while enabled, UP has priority (increments).
    up_precedence_over_down: assert property (
        @(posedge clk) disable iff (reset)
            (en_count == 4'd2) && enUP && enDOWN
            |=> (bcd8_to_int(data_MM) == inc_mod60(bcd8_to_int($past(data_MM))))
    );

    // Wrap on UP from 59 to 00 when enabled.
    wrap_up_59_to_00: assert property (
        @(posedge clk) disable iff (reset)
            (en_count == 4'd2) && enUP && (bcd8_to_int(data_MM) == 59)
            |=> (bcd8_to_int(data_MM) == 0)
    );

    ///// Down-count behavior /////
    // When enabled with enDOWN and enUP LOW, decrement modulo 60.
    dec_on_down_enabled_no_up: assert property (
        @(posedge clk) disable iff (reset)
            (en_count == 4'd2) && !enUP && enDOWN
            |=> (bcd8_to_int(data_MM) == dec_mod60(bcd8_to_int($past(data_MM))))
    );

    // Wrap on DOWN from 00 to 59 when enabled and UP is LOW.
    wrap_down_00_to_59: assert property (
        @(posedge clk) disable iff (reset)
            (en_count == 4'd2) && !enUP && enDOWN && (bcd8_to_int(data_MM) == 0)
            |=> (bcd8_to_int(data_MM) == 59)
    );

endmodule