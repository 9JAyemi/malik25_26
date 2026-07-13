module binary_counter_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [1:0] out
);

    // Helper: exact truth-table mapping from in to out
    function automatic logic [1:0] expected_out (input logic [3:0] v);
        case (v)
            4'b0000: expected_out = 2'b00;
            4'b0001: expected_out = 2'b01;
            4'b0010: expected_out = 2'b01;
            4'b0011: expected_out = 2'b10;
            4'b0100: expected_out = 2'b01;
            4'b0101: expected_out = 2'b10;
            4'b0110: expected_out = 2'b10;
            4'b0111: expected_out = 2'b11;
            4'b1000: expected_out = 2'b01;
            4'b1001: expected_out = 2'b10;
            4'b1010: expected_out = 2'b10;
            4'b1011: expected_out = 2'b11;
            4'b1100: expected_out = 2'b10;
            4'b1101: expected_out = 2'b11;
            4'b1110: expected_out = 2'b11;
            4'b1111: expected_out = 2'b10;
            default: expected_out = 2'b00;
        endcase
    endfunction

    ///// Functional mapping /////
    // Out must match the truth table for every input.
    check_truth_table: assert property (
        @(posedge clk) out == expected_out(in)
    );

    ///// Inverse mapping (consistency) /////
    // If out is 00, input must be 0000.
    check_inverse_out_00: assert property (
        @(posedge clk) (out == 2'b00) |-> (in == 4'b0000)
    );
    // If out is 01, input must be one of single-bit-set values.
    check_inverse_out_01: assert property (
        @(posedge clk) (out == 2'b01) |-> (in inside {4'b0001,4'b0010,4'b0100,4'b1000})
    );
    // If out is 10, input must be one of the specified seven values.
    check_inverse_out_10: assert property (
        @(posedge clk) (out == 2'b10) |-> (in inside {4'b0011,4'b0101,4'b0110,4'b1001,4'b1010,4'b1100,4'b1111})
    );
    // If out is 11, input must be one of the three-ones values.
    check_inverse_out_11: assert property (
        @(posedge clk) (out == 2'b11) |-> (in inside {4'b0111,4'b1011,4'b1101,4'b1110})
    );

    ///// Forward mapping by input classes /////
    // If input has exactly one bit set, out must be 01.
    check_onehot_implies_01: assert property (
        @(posedge clk) (in inside {4'b0001,4'b0010,4'b0100,4'b1000}) |-> (out == 2'b01)
    );
    // If input has exactly two bits set, out must be 10.
    check_two_ones_implies_10: assert property (
        @(posedge clk) (in inside {4'b0011,4'b0101,4'b0110,4'b1001,4'b1010,4'b1100}) |-> (out == 2'b10)
    );
    // If input has exactly three bits set, out must be 11.
    check_three_ones_implies_11: assert property (
        @(posedge clk) (in inside {4'b0111,4'b1011,4'b1101,4'b1110}) |-> (out == 2'b11)
    );
    // If input has zero bits set, out must be 00.
    check_zero_ones_implies_00: assert property (
        @(posedge clk) (in == 4'b0000) |-> (out == 2'b00)
    );
    // If input has four bits set, out must be 10 (special case in RTL).
    check_four_ones_implies_10: assert property (
        @(posedge clk) (in == 4'b1111) |-> (out == 2'b10)
    );

    ///// Stability /////
    // If input is stable across a cycle, output remains stable.
    check_stable_when_input_stable: assert property (
        @(posedge clk) $stable(in) |-> $stable(out)
    );

endmodule