module bit_converter_sva (
    input logic CLK,
    input logic [3:0] in,
    input logic [1:0] out
);
    // Out must equal the RTL ternary expression for all inputs.
    check_function_equivalence: assert property (
        @(posedge CLK) out == ((in < 4'd5) ? 2'b00 :
                               (in < 4'd9) ? 2'b01 :
                               (in < 4'd11) ? 2'b10 : 2'b11)
    );

    // For in=0..4, out must be 00.
    check_out_for_in_lt_5: assert property (
        @(posedge CLK) (in < 4'd5) |-> (out == 2'b00)
    );

    // For in=5..8, out must be 01.
    check_out_for_5_to_8: assert property (
        @(posedge CLK) (in >= 4'd5 && in < 4'd9) |-> (out == 2'b01)
    );

    // For in=9..10, out must be 10.
    check_out_for_9_to_10: assert property (
        @(posedge CLK) (in >= 4'd9 && in < 4'd11) |-> (out == 2'b10)
    );

    // For in=11..15, out must be 11.
    check_out_for_11_to_15: assert property (
        @(posedge CLK) (in >= 4'd11) |-> (out == 2'b11)
    );

    // If out is 00, in must be 0..4.
    check_in_range_when_out_00: assert property (
        @(posedge CLK) (out == 2'b00) |-> (in < 4'd5)
    );

    // If out is 01, in must be 5..8.
    check_in_range_when_out_01: assert property (
        @(posedge CLK) (out == 2'b01) |-> (in >= 4'd5 && in < 4'd9)
    );

    // If out is 10, in must be 9..10.
    check_in_range_when_out_10: assert property (
        @(posedge CLK) (out == 2'b10) |-> (in >= 4'd9 && in < 4'd11)
    );

    // If out is 11, in must be 11..15.
    check_in_range_when_out_11: assert property (
        @(posedge CLK) (out == 2'b11) |-> (in >= 4'd11)
    );

    // If input is stable across cycles, output must be stable.
    check_stability: assert property (
        @(posedge CLK) $stable(in) |-> $stable(out)
    );
endmodule