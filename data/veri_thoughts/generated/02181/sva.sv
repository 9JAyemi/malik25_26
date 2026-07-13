module top_module_sva (
    input logic CLK,
    input logic reset,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] C,
    input logic UP_DOWN,
    input logic [7:0] out,
    input logic [3:0] conditional_output_result,
    input logic [2:0] up_down_counter_result
);
    ///// conditional_output behavior /////
    // When C==00, conditional_output_result equals A.
    sel_c00_is_a: assert property (
        @(posedge CLK) disable iff (reset) (C == 2'b00) |-> (conditional_output_result == A)
    );
    // When C==01, conditional_output_result equals B.
    sel_c01_is_b: assert property (
        @(posedge CLK) disable iff (reset) (C == 2'b01) |-> (conditional_output_result == B)
    );
    // When C==10, conditional_output_result equals A ^ B.
    sel_c10_is_xor: assert property (
        @(posedge CLK) disable iff (reset) (C == 2'b10) |-> (conditional_output_result == (A ^ B))
    );
    // When C==11, conditional_output_result equals 0.
    sel_c11_is_zero: assert property (
        @(posedge CLK) disable iff (reset) (C == 2'b11) |-> (conditional_output_result == 4'b0000)
    );

    ///// up_down_counter behavior /////
    // On UP, counter increments with wrap at 7->0.
    counter_inc_rule: assert property (
        @(posedge CLK) disable iff (reset)
            ($past(!reset) && (UP_DOWN == 1'b1)) |-> (up_down_counter_result ==
                (($past(up_down_counter_result) == 3'b111) ? 3'b000 : ($past(up_down_counter_result) + 1'b1)))
    );
    // On DOWN, counter decrements with wrap at 0->7.
    counter_dec_rule: assert property (
        @(posedge CLK) disable iff (reset)
            ($past(!reset) && (UP_DOWN == 1'b0)) |-> (up_down_counter_result ==
                (($past(up_down_counter_result) == 3'b000) ? 3'b111 : ($past(up_down_counter_result) - 1'b1)))
    );
    // Explicit wrap on UP from 7 to 0.
    counter_wrap_up_from_7: assert property (
        @(posedge CLK) disable iff (reset)
            ($past(!reset) && (UP_DOWN == 1'b1) && ($past(up_down_counter_result) == 3'b111)) |-> (up_down_counter_result == 3'b000)
    );
    // Explicit wrap on DOWN from 0 to 7.
    counter_wrap_down_from_0: assert property (
        @(posedge CLK) disable iff (reset)
            ($past(!reset) && (UP_DOWN == 1'b0) && ($past(up_down_counter_result) == 3'b000)) |-> (up_down_counter_result == 3'b111)
    );
    // Counter changes every cycle by design (no hold state).
    counter_progress_each_cycle: assert property (
        @(posedge CLK) disable iff (reset) $past(!reset) |-> (up_down_counter_result != $past(up_down_counter_result))
    );

    ///// sum_module behavior /////
    // Sum output equals {conditional_output_result, {1'b0, counter}} + counter.
    sum_matches_operands: assert property (
        @(posedge CLK) disable iff (reset)
            out == ({conditional_output_result, {1'b0, up_down_counter_result}} + {5'b00000, up_down_counter_result})
    );
    // LSB of out is always 0 since the two LSB addends are identical.
    lsb_always_zero: assert property (
        @(posedge CLK) disable iff (reset) (out[0] == 1'b0)
    );
endmodule