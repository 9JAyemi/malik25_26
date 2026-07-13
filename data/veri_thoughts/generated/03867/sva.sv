module top_module_sva (
    input logic       clk,
    input logic       reset,
    input logic       enable,
    input logic       select,
    input logic [3:0] out,
    input logic [1:0] decoder_out,
    input logic [3:0] counter_out,
    input logic [3:0] func_out
);

    // Decoder loads 00 when enable is high.
    check_decoder_enable_forces_zero: assert property (
        @(posedge clk) disable iff (reset)
        enable |=> (decoder_out == 2'b00)
    );

    // Decoder advances from 00 to 01 when enable is low.
    check_decoder_step_00_to_01: assert property (
        @(posedge clk) disable iff (reset)
        (!enable && (decoder_out == 2'b00)) |=> (decoder_out == 2'b01)
    );

    // Decoder advances from 01 to 10 when enable is low.
    check_decoder_step_01_to_10: assert property (
        @(posedge clk) disable iff (reset)
        (!enable && (decoder_out == 2'b01)) |=> (decoder_out == 2'b10)
    );

    // Decoder advances from 10 to 11 when enable is low.
    check_decoder_step_10_to_11: assert property (
        @(posedge clk) disable iff (reset)
        (!enable && (decoder_out == 2'b10)) |=> (decoder_out == 2'b11)
    );

    // Decoder advances from 11 to 00 when enable is low.
    check_decoder_step_11_to_00: assert property (
        @(posedge clk) disable iff (reset)
        (!enable && (decoder_out == 2'b11)) |=> (decoder_out == 2'b00)
    );

    // Counter clears to zero on reset.
    check_counter_reset_clears: assert property (
        @(posedge clk)
        reset |=> (counter_out == 4'b0000)
    );

    // Counter increments by one when its enable is high.
    check_counter_increments_when_enabled: assert property (
        @(posedge clk) disable iff (reset)
        decoder_out[0] |=> (counter_out == ($past(counter_out) + 4'd1))
    );

    // Counter holds its value when its enable is low.
    check_counter_holds_when_disabled: assert property (
        @(posedge clk) disable iff (reset)
        !decoder_out[0] |=> (counter_out == $past(counter_out))
    );

    // Functional module clears to zero on reset.
    check_func_reset_clears: assert property (
        @(posedge clk)
        reset |=> (func_out == 4'b0000)
    );

    // Functional module outputs counter input plus one when selected.
    check_func_updates_when_selected: assert property (
        @(posedge clk) disable iff (reset)
        select |=> (func_out == ($past(counter_out) + 4'd1))
    );

    // Functional module holds its value when select is low.
    check_func_holds_when_not_selected: assert property (
        @(posedge clk) disable iff (reset)
        !select |=> (func_out == $past(func_out))
    );

    // Top output clears to zero on reset.
    check_top_reset_clears_out: assert property (
        @(posedge clk)
        reset |=> (out == 4'b0000)
    );

    // Top output takes the functional path when decoder_out[1] is high.
    check_top_selects_func_path: assert property (
        @(posedge clk) disable iff (reset)
        decoder_out[1] |=> (out == $past(func_out))
    );

    // Top output takes the counter path when decoder_out[1] is low.
    check_top_selects_counter_path: assert property (
        @(posedge clk) disable iff (reset)
        !decoder_out[1] |=> (out == $past(counter_out))
    );

endmodule