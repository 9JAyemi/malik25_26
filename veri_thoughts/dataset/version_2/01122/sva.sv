module mux_6to1_sva (
    input logic [2:0] sel,
    input logic [23:0] data_in,
    input logic [3:0] out
);
    ///// Functional mapping checks /////
    // sel=000 selects data_in[3:0].
    sel_000_selects_low_nibble: assert property (
        @(posedge $global_clock) (sel == 3'b000) |-> (out == data_in[3:0])
    );
    // sel=001 selects data_in[7:4].
    sel_001_selects_nibble1: assert property (
        @(posedge $global_clock) (sel == 3'b001) |-> (out == data_in[7:4])
    );
    // sel=010 selects data_in[11:8].
    sel_010_selects_nibble2: assert property (
        @(posedge $global_clock) (sel == 3'b010) |-> (out == data_in[11:8])
    );
    // sel=011 selects data_in[15:12].
    sel_011_selects_nibble3: assert property (
        @(posedge $global_clock) (sel == 3'b011) |-> (out == data_in[15:12])
    );
    // sel=100 selects data_in[19:16].
    sel_100_selects_nibble4: assert property (
        @(posedge $global_clock) (sel == 3'b100) |-> (out == data_in[19:16])
    );
    // sel=101 selects data_in[23:20].
    sel_101_selects_nibble5: assert property (
        @(posedge $global_clock) (sel == 3'b101) |-> (out == data_in[23:20])
    );
    // sel=110/111 drives out to 0 (default case).
    default_sel_outputs_zero: assert property (
        @(posedge $global_clock) (sel[2:1] == 2'b11) |-> (out == 4'b0000)
    );

    ///// General combinational properties /////
    // Out equals one of the six nibbles or zero.
    out_matches_allowed_values: assert property (
        @(posedge $global_clock)
            (out == data_in[3:0])  ||
            (out == data_in[7:4])  ||
            (out == data_in[11:8]) ||
            (out == data_in[15:12])||
            (out == data_in[19:16])||
            (out == data_in[23:20])||
            (out == 4'b0000)
    );
    // Out only changes when sel or data_in changes.
    out_changes_only_with_inputs: assert property (
        @(posedge $global_clock) $changed(out) |-> $changed({sel, data_in})
    );
    // If sel and data_in are stable, out is stable.
    out_stable_when_inputs_stable: assert property (
        @(posedge $global_clock) $stable({sel, data_in}) |-> $stable(out)
    );
endmodule