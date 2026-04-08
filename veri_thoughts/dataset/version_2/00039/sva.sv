module Deco_Round_Mult_sva (
    input logic       clk,
    input logic [1:0] round_mode,
    input logic       or_info,
    input logic       xor_info,
    input logic       ctrl
);

    // 0101 decodes ctrl low.
    check_case_0101_ctrl_low: assert property (
        @(posedge clk)
        ({xor_info, or_info, round_mode} == 4'b0101) |-> (ctrl == 1'b0)
    );

    // 1101 decodes ctrl high.
    check_case_1101_ctrl_high: assert property (
        @(posedge clk)
        ({xor_info, or_info, round_mode} == 4'b1101) |-> (ctrl == 1'b1)
    );

    // 0110 decodes ctrl high.
    check_case_0110_ctrl_high: assert property (
        @(posedge clk)
        ({xor_info, or_info, round_mode} == 4'b0110) |-> (ctrl == 1'b1)
    );

    // 1110 decodes ctrl low.
    check_case_1110_ctrl_low: assert property (
        @(posedge clk)
        ({xor_info, or_info, round_mode} == 4'b1110) |-> (ctrl == 1'b0)
    );

    // All unspecified input combinations drive ctrl low.
    check_default_ctrl_low: assert property (
        @(posedge clk)
        (({xor_info, or_info, round_mode} != 4'b0101) &&
         ({xor_info, or_info, round_mode} != 4'b1101) &&
         ({xor_info, or_info, round_mode} != 4'b0110) &&
         ({xor_info, or_info, round_mode} != 4'b1110)) |-> (ctrl == 1'b0)
    );

    // ctrl can only be high for the two explicit high-output cases.
    check_ctrl_high_only_on_explicit_high_cases: assert property (
        @(posedge clk)
        ctrl |-> (({xor_info, or_info, round_mode} == 4'b1101) ||
                  ({xor_info, or_info, round_mode} == 4'b0110))
    );

    // ctrl exactly matches the case decode.
    check_ctrl_matches_case_decode: assert property (
        @(posedge clk)
        ctrl == ((({xor_info, or_info, round_mode} == 4'b1101) ||
                  ({xor_info, or_info, round_mode} == 4'b0110)) ? 1'b1 : 1'b0)
    );

endmodule