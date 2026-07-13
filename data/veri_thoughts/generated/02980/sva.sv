module mux16to1_sva (
    input logic clk,          // sampling clock for SVA only
    input logic [15:0] data_in,
    input logic [3:0] select,
    input logic data_out
);

    // For known select values (no X/Z), output equals the selected input bit.
    pass_through_known_select: assert property (
        @(posedge clk) !$isunknown(select) |=> (data_out === data_in[select])
    );

    // If select contains X/Z, default branch drives output LOW.
    default_on_unknown_select: assert property (
        @(posedge clk) $isunknown(select) |=> (data_out === 1'b0)
    );

    // When select==0, output equals data_in[0].
    pass_through_sel0: assert property (
        @(posedge clk) (select == 4'd0) |=> (data_out === data_in[0])
    );

    // When select==1, output equals data_in[1].
    pass_through_sel1: assert property (
        @(posedge clk) (select == 4'd1) |=> (data_out === data_in[1])
    );

    // When select==7, output equals data_in[7].
    pass_through_sel7: assert property (
        @(posedge clk) (select == 4'd7) |=> (data_out === data_in[7])
    );

    // When select==8, output equals data_in[8].
    pass_through_sel8: assert property (
        @(posedge clk) (select == 4'd8) |=> (data_out === data_in[8])
    );

    // When select==15, output equals data_in[15].
    pass_through_sel15: assert property (
        @(posedge clk) (select == 4'd15) |=> (data_out === data_in[15])
    );

    // If all inputs are 0, output must be 0 for any select (known or unknown).
    zero_inputs_drive_zero: assert property (
        @(posedge clk) (data_in == 16'b0) |=> (data_out === 1'b0)
    );

    // If all inputs are 1 and select is known, output is 1.
    ones_inputs_drive_one_when_select_known: assert property (
        @(posedge clk) (!$isunknown(select) && (data_in == 16'hFFFF)) |=> (data_out === 1'b1)
    );

    // With select and the selected input bit stable across cycles, output stays stable.
    stable_output_when_select_and_selected_input_stable: assert property (
        @(posedge clk) (!$isunknown(select) && !$isunknown($past(select)) && (select == $past(select)) && ($past(data_in[select]) === data_in[select])) |=> (data_out === $past(data_out))
    );

endmodule