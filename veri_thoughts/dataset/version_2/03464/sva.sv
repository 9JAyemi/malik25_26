module Registro_Universal_sva
#(parameter N = 8) (
    input logic hold,
    input logic [N-1:0] in_rtc_dato,
    input logic [N-1:0] in_count_dato,
    input logic clk,
    input logic reset,
    input logic chip_select,
    input logic [N-1:0] out_dato
);

    // A sampled reset leaves the output cleared by the next clock sample.
    check_reset_clears_output: assert property (
        @(negedge clk) reset |=> (out_dato == '0)
    );

    // Hold keeps the register output unchanged.
    check_hold_preserves_value: assert property (
        @(negedge clk) disable iff (reset)
        hold |=> (out_dato == $past(out_dato))
    );

    // With hold low and chip_select low, the RTC input is loaded.
    check_loads_rtc_input: assert property (
        @(negedge clk) disable iff (reset)
        (!hold && (chip_select == 1'b0)) |=> (out_dato == $past(in_rtc_dato))
    );

    // With hold low and chip_select high, the count input is loaded.
    check_loads_count_input: assert property (
        @(negedge clk) disable iff (reset)
        (!hold && (chip_select == 1'b1)) |=> (out_dato == $past(in_count_dato))
    );

endmodule