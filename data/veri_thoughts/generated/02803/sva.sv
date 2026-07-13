module counter_sva (
    input logic clk,
    input logic [3:0] out
);
    ///// Counter behavior /////
    // Next value follows: wrap to 0 after 15, else increment by 1 (once previous value is known).
    check_next_value_function: assert property (
        @(posedge clk) !$isunknown($past(out)) |-> (out == (($past(out) == 4'hF) ? 4'h0 : $past(out) + 4'd1))
    );

    // After 15, counter wraps to 0 (once previous value is known).
    check_wrap_when_max: assert property (
        @(posedge clk) (!$isunknown($past(out)) && ($past(out) == 4'hF)) |-> (out == 4'h0)
    );

    // When not 15, counter increments by 1 (once previous value is known).
    check_increment_when_not_max: assert property (
        @(posedge clk) (!$isunknown($past(out)) && ($past(out) != 4'hF)) |-> (out == $past(out) + 4'd1)
    );

    // Value never holds its previous value (once previous value is known).
    check_no_stutter: assert property (
        @(posedge clk) !$isunknown($past(out)) |-> (out != $past(out))
    );

    // Zero appears only after 15 (once previous value is known).
    check_zero_only_from_wrap: assert property (
        @(posedge clk) (!$isunknown($past(out)) && (out == 4'h0)) |-> ($past(out) == 4'hF)
    );

    // LSB toggles every cycle (once previous value is known).
    check_lsb_toggle: assert property (
        @(posedge clk) !$isunknown($past(out[0])) |-> (out[0] == ~ $past(out[0]))
    );

    // Bit1 toggles iff previous LSB was 1 (once previous value is known).
    check_bit1_toggle_on_carry: assert property (
        @(posedge clk) !$isunknown($past(out[1:0])) |-> (out[1] == ($past(out[0]) ? ~ $past(out[1]) : $past(out[1])))
    );

    // Bit2 toggles iff previous [1:0] were 2'b11 (once previous value is known).
    check_bit2_toggle_on_carry: assert property (
        @(posedge clk) !$isunknown($past(out[2:0])) |-> (out[2] == (($past(out[1:0]) == 2'b11) ? ~ $past(out[2]) : $past(out[2])))
    );

    // Bit3 toggles iff previous [2:0] were 3'b111 (once previous value is known).
    check_bit3_toggle_on_carry: assert property (
        @(posedge clk) !$isunknown($past(out[3:0])) |-> (out[3] == (($past(out[2:0]) == 3'b111) ? ~ $past(out[3]) : $past(out[3])))
    );

    // Out is not zero unless previous was 15 (once previous value is known).
    check_no_zero_without_wrap: assert property (
        @(posedge clk) (!$isunknown($past(out)) && ($past(out) != 4'hF)) |-> (out != 4'h0)
    );
endmodule