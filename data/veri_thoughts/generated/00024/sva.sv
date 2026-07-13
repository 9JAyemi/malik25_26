module top_module_sva (
    input logic [7:0] in1,
    input logic [7:0] in2,
    input logic [2:0] pos_diff
);

    function automatic logic [2:0] encode_pos(input logic [7:0] in);
        begin
            case (in)
                8'b0000_0001: encode_pos = 3'b000;
                8'b0000_0010: encode_pos = 3'b001;
                8'b0000_0100: encode_pos = 3'b010;
                8'b0000_1000: encode_pos = 3'b011;
                8'b0001_0000: encode_pos = 3'b100;
                8'b0010_0000: encode_pos = 3'b101;
                8'b0100_0000: encode_pos = 3'b110;
                default:      encode_pos = 3'b111;
            endcase
        end
    endfunction

    function automatic logic [2:0] expected_diff(
        input logic [7:0] a,
        input logic [7:0] b
    );
        begin
            expected_diff = encode_pos(a) - encode_pos(b);
        end
    endfunction

    // Output matches the encoded-position difference for all inputs.
    check_pos_diff_matches_encoded_difference: assert property (
        @($global_clock) pos_diff == expected_diff(in1, in2)
    );

    // With in2 at position 0, bit 0 on in1 produces difference 0.
    check_in1_bit0_maps_to_zero: assert property (
        @($global_clock) (in2 == 8'b0000_0001 && in1 == 8'b0000_0001) |-> (pos_diff == 3'b000)
    );

    // With in2 at position 0, bit 1 on in1 produces difference 1.
    check_in1_bit1_maps_to_one: assert property (
        @($global_clock) (in2 == 8'b0000_0001 && in1 == 8'b0000_0010) |-> (pos_diff == 3'b001)
    );

    // With in2 at position 0, bit 2 on in1 produces difference 2.
    check_in1_bit2_maps_to_two: assert property (
        @($global_clock) (in2 == 8'b0000_0001 && in1 == 8'b0000_0100) |-> (pos_diff == 3'b010)
    );

    // With in2 at position 0, bit 3 on in1 produces difference 3.
    check_in1_bit3_maps_to_three: assert property (
        @($global_clock) (in2 == 8'b0000_0001 && in1 == 8'b0000_1000) |-> (pos_diff == 3'b011)
    );

    // With in2 at position 0, bit 4 on in1 produces difference 4.
    check_in1_bit4_maps_to_four: assert property (
        @($global_clock) (in2 == 8'b0000_0001 && in1 == 8'b0001_0000) |-> (pos_diff == 3'b100)
    );

    // With in2 at position 0, bit 5 on in1 produces difference 5.
    check_in1_bit5_maps_to_five: assert property (
        @($global_clock) (in2 == 8'b0000_0001 && in1 == 8'b0010_0000) |-> (pos_diff == 3'b101)
    );

    // With in2 at position 0, bit 6 on in1 produces difference 6.
    check_in1_bit6_maps_to_six: assert property (
        @($global_clock) (in2 == 8'b0000_0001 && in1 == 8'b0100_0000) |-> (pos_diff == 3'b110)
    );

    // With in2 at position 0, all other in1 values map to 7.
    check_in1_default_maps_to_seven: assert property (
        @($global_clock)
        (in2 == 8'b0000_0001 &&
         !(in1 == 8'b0000_0001 ||
           in1 == 8'b0000_0010 ||
           in1 == 8'b0000_0100 ||
           in1 == 8'b0000_1000 ||
           in1 == 8'b0001_0000 ||
           in1 == 8'b0010_0000 ||
           in1 == 8'b0100_0000)) |-> (pos_diff == 3'b111)
    );

    // With in1 at position 0, all other in2 values subtract as encoded 7.
    check_in2_default_maps_to_one: assert property (
        @($global_clock)
        (in1 == 8'b0000_0001 &&
         !(in2 == 8'b0000_0001 ||
           in2 == 8'b0000_0010 ||
           in2 == 8'b0000_0100 ||
           in2 == 8'b0000_1000 ||
           in2 == 8'b0001_0000 ||
           in2 == 8'b0010_0000 ||
           in2 == 8'b0100_0000)) |-> (pos_diff == 3'b001)
    );

endmodule