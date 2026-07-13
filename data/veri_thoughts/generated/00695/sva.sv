module edge_detector_sva (
    input logic clk,
    input logic [7:0] in,
    input logic [7:0] anyedge
);

    ///// Output encoding constraints /////
    // anyedge can only be 8'h00 (IDLE), 8'h01 (RISING_EDGE code), or 8'h02 (FALLING_EDGE code).
    check_anyedge_value_set: assert property (
        @(posedge clk) anyedge inside {8'h00, 8'h01, 8'h02}
    );

    ///// Functional mapping from previous/current input difference /////
    // One-hot XOR between $past(in) and in selects 8'h01.
    check_onehot_xor_gives_01: assert property (
        @(posedge clk) $onehot($past(in) ^ in) |-> (anyedge == 8'h01)
    );

    // One-cold XOR (i.e., complement is one-hot) selects 8'h02.
    check_onecold_xor_gives_02: assert property (
        @(posedge clk) $onehot(~($past(in) ^ in)) |-> (anyedge == 8'h02)
    );

    // If XOR is neither one-hot nor one-cold, anyedge is 8'h00.
    check_default_gives_00: assert property (
        @(posedge clk) !($onehot($past(in) ^ in) || $onehot(~($past(in) ^ in))) |-> (anyedge == 8'h00)
    );

    ///// Useful special cases /////
    // If input does not change, anyedge is 8'h00.
    check_no_change_idle: assert property (
        @(posedge clk) ($past(in) == in) |-> (anyedge == 8'h00)
    );

    // If all bits toggle, anyedge is 8'h00 (falls into default case).
    check_all_bits_toggle_idle: assert property (
        @(posedge clk) (($past(in) ^ in) == 8'hFF) |-> (anyedge == 8'h00)
    );

    ///// Reverse implications (consistency) /////
    // anyedge == 8'h01 implies XOR was one-hot.
    check_01_implies_onehot: assert property (
        @(posedge clk) (anyedge == 8'h01) |-> $onehot($past(in) ^ in)
    );

    // anyedge == 8'h02 implies XOR was one-cold.
    check_02_implies_onecold: assert property (
        @(posedge clk) (anyedge == 8'h02) |-> $onehot(~($past(in) ^ in))
    );

    // anyedge == 8'h00 implies XOR was neither one-hot nor one-cold.
    check_00_implies_neither: assert property (
        @(posedge clk) (anyedge == 8'h00) |-> !($onehot($past(in) ^ in) || $onehot(~($past(in) ^ in)))
    );

    ///// Structural encoding /////
    // Upper 6 bits of anyedge are always zero due to 8'h00/01/02 assignments.
    check_upper_bits_zero: assert property (
        @(posedge clk) anyedge[7:2] == 6'b0
    );

endmodule