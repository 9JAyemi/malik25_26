module top_module_sva (
    input logic [7:0] in,
    input logic [2:0] pos,
    input logic [15:0] in2,
    input logic [7:0] out_hi,
    input logic [7:0] out_lo,
    input logic enable,
    input logic [15:0] out_sum
);

    function automatic logic [2:0] expected_pos(input logic [7:0] value);
        begin
            case (value)
                8'b00000001: expected_pos = 3'b000;
                8'b00000010: expected_pos = 3'b001;
                8'b00000100: expected_pos = 3'b010;
                8'b00001000: expected_pos = 3'b011;
                8'b00010000: expected_pos = 3'b100;
                8'b00100000: expected_pos = 3'b101;
                8'b01000000: expected_pos = 3'b110;
                8'b10000000: expected_pos = 3'b111;
                default:      expected_pos = 3'b000;
            endcase
        end
    endfunction

    // One-hot inputs map to the asserted bit index.
    check_pos_onehot_maps_to_bit: assert property (
        @(posedge enable) $onehot(in) |-> (in == (8'b00000001 << pos))
    );

    // Non-one-hot inputs use the default zero position.
    check_pos_non_onehot_defaults_zero: assert property (
        @(posedge enable) !$onehot(in) |-> (pos == 3'b000)
    );

    // pos follows the encoder case mapping.
    check_pos_matches_encoder_case: assert property (
        @(posedge enable) pos == expected_pos(in)
    );

    // out_hi is the upper byte of in2.
    check_out_hi_upper_byte: assert property (
        @(posedge enable) out_hi == in2[15:8]
    );

    // out_lo is the lower byte of in2.
    check_out_lo_lower_byte: assert property (
        @(posedge enable) out_lo == in2[7:0]
    );

    // The byte outputs reconstruct the original input word.
    check_out_bytes_reconstruct_input: assert property (
        @(posedge enable) {out_hi, out_lo} == in2
    );

    // out_sum holds the previous enable-edge sum from the visible outputs.
    check_out_sum_captures_previous_visible_sum: assert property (
        @(posedge enable) 1'b1 |=> (out_sum == $past({pos, 3'b000} + {out_hi, out_lo}))
    );

    // out_sum also matches the previous enable-edge sum from in and in2.
    check_out_sum_captures_previous_input_sum: assert property (
        @(posedge enable) 1'b1 |=> (out_sum == $past({expected_pos(in), 3'b000} + in2))
    );

endmodule