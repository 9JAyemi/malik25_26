module priority_encoder_sva (
    input logic CLK,
    input logic [3:0] in,
    input logic [1:0] out
);
    // Golden model of the combinational encoding.
    function automatic logic [1:0] expected_out (input logic [3:0] vin);
        case (vin)
            4'b0001: expected_out = 2'b00;
            4'b0010: expected_out = 2'b01;
            4'b0100: expected_out = 2'b10;
            4'b1000: expected_out = 2'b11;
            default: expected_out = 2'b00;
        endcase
    endfunction

    // Output matches the case-encoded mapping for all inputs.
    check_functional_mapping: assert property (
        @(posedge CLK) out == expected_out(in)
    );

    // When in is 0001, out is 00.
    check_map_0001: assert property (
        @(posedge CLK) (in == 4'b0001) |=> (out == 2'b00)
    );

    // When in is 0010, out is 01.
    check_map_0010: assert property (
        @(posedge CLK) (in == 4'b0010) |=> (out == 2'b01)
    );

    // When in is 0100, out is 10.
    check_map_0100: assert property (
        @(posedge CLK) (in == 4'b0100) |=> (out == 2'b10)
    );

    // When in is 1000, out is 11.
    check_map_1000: assert property (
        @(posedge CLK) (in == 4'b1000) |=> (out == 2'b11)
    );

    // When in is 0000, out is 00 due to default.
    check_map_0000_default: assert property (
        @(posedge CLK) (in == 4'b0000) |=> (out == 2'b00)
    );

    // For any non-onehot input, out defaults to 00.
    check_non_onehot_defaults_zero: assert property (
        @(posedge CLK) (!(in == 4'b0001 || in == 4'b0010 || in == 4'b0100 || in == 4'b1000)) |=> (out == 2'b00)
    );
endmodule