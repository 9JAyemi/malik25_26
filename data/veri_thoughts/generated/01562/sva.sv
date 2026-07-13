module data_comp_decomp_sva (
    input logic CLK,          // sampling clock for SVA (DUT is combinational)
    input logic [7:0] data_in,
    input logic [3:0] data_out,
    input logic       valid
);
    // Analysis: no clock/reset in DUT; purely combinational; maps 4 encodings, else invalid.

    // data_in == 8'h01 maps to data_out == 4'h1 with valid == 1
    check_map_sym1: assert property (
        @(posedge CLK) (data_in == 8'h01) |-> ((data_out == 4'h1) && (valid == 1'b1))
    );

    // data_in == 8'h02 maps to data_out == 4'h2 with valid == 1
    check_map_sym2: assert property (
        @(posedge CLK) (data_in == 8'h02) |-> ((data_out == 4'h2) && (valid == 1'b1))
    );

    // data_in == 8'h04 maps to data_out == 4'h3 with valid == 1
    check_map_sym3: assert property (
        @(posedge CLK) (data_in == 8'h04) |-> ((data_out == 4'h3) && (valid == 1'b1))
    );

    // data_in == 8'h08 maps to data_out == 4'h4 with valid == 1
    check_map_sym4: assert property (
        @(posedge CLK) (data_in == 8'h08) |-> ((data_out == 4'h4) && (valid == 1'b1))
    );

    // For all other data_in values, data_out == 0 and valid == 0
    check_default_map: assert property (
        @(posedge CLK) !(data_in inside {8'h01,8'h02,8'h04,8'h08}) |-> ((data_out == 4'h0) && (valid == 1'b0))
    );

    // valid == 1 occurs only for recognized inputs
    check_valid_high_implies_recognized: assert property (
        @(posedge CLK) (valid == 1'b1) |-> (data_in inside {8'h01,8'h02,8'h04,8'h08})
    );

    // Recognized inputs always produce valid == 1
    check_recognized_implies_valid_high: assert property (
        @(posedge CLK) (data_in inside {8'h01,8'h02,8'h04,8'h08}) |-> (valid == 1'b1)
    );

    // valid == 0 implies data_out == 0
    check_valid_low_implies_zero: assert property (
        @(posedge CLK) (valid == 1'b0) |-> (data_out == 4'h0)
    );

    // data_out == 0 implies valid == 0
    check_zero_implies_valid_low: assert property (
        @(posedge CLK) (data_out == 4'h0) |-> (valid == 1'b0)
    );

    // Non-zero data_out implies recognized input and valid == 1
    check_nonzero_out_implies_recognized_and_valid: assert property (
        @(posedge CLK) (data_out != 4'h0) |-> ((data_in inside {8'h01,8'h02,8'h04,8'h08}) && (valid == 1'b1))
    );

    // valid == 1 implies data_out is one of 4'h1..4'h4
    check_valid_high_implies_known_code: assert property (
        @(posedge CLK) (valid == 1'b1) |-> (data_out inside {4'h1,4'h2,4'h3,4'h4})
    );
endmodule