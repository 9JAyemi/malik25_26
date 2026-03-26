module Deco_Round_Mult_sva (
    input logic clk,
    input logic [1:0] round_mode,
    input logic or_info,
    input logic xor_info,
    input logic ctrl
);

    // ctrl is high for input encoding 1101.
    check_ctrl_high_on_1101: assert property (
        @(posedge clk)
        ({xor_info, or_info, round_mode} === 4'b1101) |-> (ctrl === 1'b1)
    );

    // ctrl is high for input encoding 0110.
    check_ctrl_high_on_0110: assert property (
        @(posedge clk)
        ({xor_info, or_info, round_mode} === 4'b0110) |-> (ctrl === 1'b1)
    );

    // ctrl is low for every encoding other than the two one-driving cases.
    check_ctrl_low_on_all_other_encodings: assert property (
        @(posedge clk)
        !(({xor_info, or_info, round_mode} === 4'b1101) ||
          ({xor_info, or_info, round_mode} === 4'b0110)) |-> (ctrl === 1'b0)
    );

    // A high ctrl implies one of the two one-driving encodings.
    check_ctrl_high_only_on_defined_cases: assert property (
        @(posedge clk)
        (ctrl === 1'b1) |-> (({xor_info, or_info, round_mode} === 4'b1101) ||
                             ({xor_info, or_info, round_mode} === 4'b0110))
    );

endmodule