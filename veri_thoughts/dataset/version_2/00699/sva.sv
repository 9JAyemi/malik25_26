module mux4to1_sva (
    input logic clk,            // sampling clock for assertions
    input logic [3:0] data_in,
    input logic [1:0] sel,
    input logic data_out
);
    ///// Functional mapping /////
    // When sel is 2-state, output equals the selected input bit.
    check_mux_function_general: assert property (
        @(posedge clk) (sel inside {2'b00,2'b01,2'b10,2'b11}) |-> (data_out === data_in[sel])
    );

    // sel==00 routes data_in[0] to data_out.
    check_sel_00_route: assert property (
        @(posedge clk) (sel === 2'b00) |-> (data_out === data_in[0])
    );
    // sel==01 routes data_in[1] to data_out.
    check_sel_01_route: assert property (
        @(posedge clk) (sel === 2'b01) |-> (data_out === data_in[1])
    );
    // sel==10 routes data_in[2] to data_out.
    check_sel_10_route: assert property (
        @(posedge clk) (sel === 2'b10) |-> (data_out === data_in[2])
    );
    // sel==11 routes data_in[3] to data_out.
    check_sel_11_route: assert property (
        @(posedge clk) (sel === 2'b11) |-> (data_out === data_in[3])
    );

    ///// Change-causality /////
    // Output only changes if sel or some data_in bit changed.
    check_out_change_has_cause: assert property (
        @(posedge clk) $changed(data_out) |-> ($changed(sel) || $changed(data_in))
    );

    ///// Ignore unselected inputs /////
    // With sel==00 stable, changes on data_in[3:1] do not change data_out.
    check_ignore_unselected_00: assert property (
        @(posedge clk) (sel === 2'b00) && !$changed(sel) && !$changed(data_in[0]) && $changed(data_in[3:1]) |-> !$changed(data_out)
    );
    // With sel==01 stable, changes on data_in[3:2] or data_in[0] do not change data_out.
    check_ignore_unselected_01: assert property (
        @(posedge clk) (sel === 2'b01) && !$changed(sel) && !$changed(data_in[1]) && $changed({data_in[3:2],data_in[0]}) |-> !$changed(data_out)
    );
    // With sel==10 stable, changes on data_in[3] or data_in[1:0] do not change data_out.
    check_ignore_unselected_10: assert property (
        @(posedge clk) (sel === 2'b10) && !$changed(sel) && !$changed(data_in[2]) && $changed({data_in[3],data_in[1:0]}) |-> !$changed(data_out)
    );
    // With sel==11 stable, changes on data_in[2:0] do not change data_out.
    check_ignore_unselected_11: assert property (
        @(posedge clk) (sel === 2'b11) && !$changed(sel) && !$changed(data_in[3]) && $changed(data_in[2:0]) |-> !$changed(data_out)
    );

    ///// Selected input drives output /////
    // With sel==00 stable, a change on data_in[0] causes data_out to change.
    check_selected_change_affects_out_00: assert property (
        @(posedge clk) (sel === 2'b00) && !$changed(sel) && $changed(data_in[0]) |-> $changed(data_out)
    );
    // With sel==01 stable, a change on data_in[1] causes data_out to change.
    check_selected_change_affects_out_01: assert property (
        @(posedge clk) (sel === 2'b01) && !$changed(sel) && $changed(data_in[1]) |-> $changed(data_out)
    );
    // With sel==10 stable, a change on data_in[2] causes data_out to change.
    check_selected_change_affects_out_10: assert property (
        @(posedge clk) (sel === 2'b10) && !$changed(sel) && $changed(data_in[2]) |-> $changed(data_out)
    );
    // With sel==11 stable, a change on data_in[3] causes data_out to change.
    check_selected_change_affects_out_11: assert property (
        @(posedge clk) (sel === 2'b11) && !$changed(sel) && $changed(data_in[3]) |-> $changed(data_out)
    );
endmodule