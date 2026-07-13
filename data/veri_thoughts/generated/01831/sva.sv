module top_module_sva (
    input logic clk,
    input logic up_down,
    input logic load,
    input logic reset,
    input logic [3:0] data,
    input logic [1:0] shift_amount,
    input logic [3:0] Q
);

    // Compute expected barrel shift from inputs
    logic [3:0] shifted_expected;
    always_comb begin
        unique case (shift_amount)
            2'b00: shifted_expected = data;
            2'b01: shifted_expected = {data[2:0], data[3]};
            2'b10: shifted_expected = {data[1:0], data[3:2]};
            2'b11: shifted_expected = {data[0], data[3:1]};
        endcase
    end

    ///// Reset behavior ties sum to shifted data (counter resets to 0) /////
    // On reset with shift 00, Q equals data.
    reset_shift_00: assert property (
        @(posedge clk) reset && (shift_amount == 2'b00) |-> (Q == data)
    );
    // On reset with shift 01, Q equals {data[2:0], data[3]}.
    reset_shift_01: assert property (
        @(posedge clk) reset && (shift_amount == 2'b01) |-> (Q == {data[2:0], data[3]})
    );
    // On reset with shift 10, Q equals {data[1:0], data[3:2]}.
    reset_shift_10: assert property (
        @(posedge clk) reset && (shift_amount == 2'b10) |-> (Q == {data[1:0], data[3:2]})
    );
    // On reset with shift 11, Q equals {data[0], data[3:1]}.
    reset_shift_11: assert property (
        @(posedge clk) reset && (shift_amount == 2'b11) |-> (Q == {data[0], data[3:1]})
    );

    ///// Counter-driven sum behavior when inputs to barrel shifter are stable /////
    // With load high and stable shift inputs, Q holds its previous value.
    hold_when_load_and_inputs_stable: assert property (
        @(posedge clk) disable iff (reset)
            load && $stable({data, shift_amount}) |-> (Q == $past(Q))
    );
    // With count up, no load, and stable shift inputs, Q increments by 1 (mod 16).
    inc_when_up_inputs_stable: assert property (
        @(posedge clk) disable iff (reset)
            (!load && up_down && $stable({data, shift_amount})) |-> (Q == ($past(Q) + 4'd1))
    );
    // With count down, no load, and stable shift inputs, Q decrements by 1 (mod 16).
    dec_when_down_inputs_stable: assert property (
        @(posedge clk) disable iff (reset)
            (!load && !up_down && $stable({data, shift_amount})) |-> (Q == ($past(Q) - 4'd1))
    );

    ///// General step bound when barrel inputs are stable /////
    // With stable shift inputs, Q changes by at most 1 per cycle (or holds).
    bounded_step_with_inputs_stable: assert property (
        @(posedge clk) disable iff (reset)
            $stable({data, shift_amount}) |-> ((Q == $past(Q)) || (Q == ($past(Q) + 4'd1)) || (Q == ($past(Q) - 4'd1)))
    );

    ///// Explicit wrap-around checks /////
    // On increment from 0xF with no load and stable inputs, Q wraps to 0.
    wrap_increment_from_max: assert property (
        @(posedge clk) disable iff (reset)
            (!load && up_down && $stable({data, shift_amount}) && ($past(Q) == 4'hF)) |-> (Q == 4'h0)
    );
    // On decrement from 0x0 with no load and stable inputs, Q wraps to 0xF.
    wrap_decrement_from_min: assert property (
        @(posedge clk) disable iff (reset)
            (!load && !up_down && $stable({data, shift_amount}) && ($past(Q) == 4'h0)) |-> (Q == 4'hF)
    );

endmodule