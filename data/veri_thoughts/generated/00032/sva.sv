module logic_gate_sva (
    input logic clk,
    input logic A1,
    input logic [1:0] select,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic C1,
    input logic reset,
    input logic X,
    input logic valid
);

    // Reset forces both outputs low.
    check_reset_clears_outputs: assert property (
        @(posedge clk) disable iff (!reset)
            (X == 1'b0 && valid == 1'b0)
    );

    // Outside reset, X and valid always match.
    check_outputs_match: assert property (
        @(posedge clk) disable iff (reset)
            (X == valid)
    );

    // With select set to 00, all A inputs high drives both outputs high.
    check_select00_all_high_sets_outputs: assert property (
        @(posedge clk) disable iff (reset)
            ((select == 2'b00) && A1 && A2 && A3) |-> (X == 1'b1 && valid == 1'b1)
    );

    // With select set to 00, any low A input drives both outputs low.
    check_select00_missing_input_clears_outputs: assert property (
        @(posedge clk) disable iff (reset)
            ((select == 2'b00) && !(A1 && A2 && A3)) |-> (X == 1'b0 && valid == 1'b0)
    );

    // With select not equal to 00, A1/B1/C1 high drives both outputs high.
    check_select_nonzero_all_high_sets_outputs: assert property (
        @(posedge clk) disable iff (reset)
            (((select == 2'b01) || (select == 2'b10) || (select == 2'b11)) && A1 && B1 && C1)
            |-> (X == 1'b1 && valid == 1'b1)
    );

    // With select not equal to 00, any low selected input drives both outputs low.
    check_select_nonzero_missing_input_clears_outputs: assert property (
        @(posedge clk) disable iff (reset)
            (((select == 2'b01) || (select == 2'b10) || (select == 2'b11)) && !(A1 && B1 && C1))
            |-> (X == 1'b0 && valid == 1'b0)
    );

endmodule