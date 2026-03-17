module mux2_1_sva (
    input logic       clk,
    input logic [7:0] input1,
    input logic [7:0] input2,
    input logic       select,
    input logic [7:0] selected_out
);

    // Output matches the RTL mux expression on every sample.
    check_selected_out_matches_mux: assert property (
        @(posedge clk) selected_out === (select ? input2 : input1)
    );

    // A low select routes input1 to the output.
    check_select_low_routes_input1: assert property (
        @(posedge clk) (select === 1'b0) |-> (selected_out === input1)
    );

    // A high select routes input2 to the output.
    check_select_high_routes_input2: assert property (
        @(posedge clk) (select === 1'b1) |-> (selected_out === input2)
    );

    // If both inputs are identical, the output matches that common value.
    check_equal_inputs_match_output: assert property (
        @(posedge clk) (input1 === input2) |-> (selected_out === input1)
    );

    // With stable inputs and select, the output remains stable.
    check_stable_inputs_keep_output_stable: assert property (
        @(posedge clk) ($stable(input1) && $stable(input2) && $stable(select)) |-> $stable(selected_out)
    );

    // A select change with stable data updates the output to the newly selected input.
    check_select_change_updates_output: assert property (
        @(posedge clk) ($changed(select) && $stable(input1) && $stable(input2)) |-> (selected_out === (select ? input2 : input1))
    );

endmodule