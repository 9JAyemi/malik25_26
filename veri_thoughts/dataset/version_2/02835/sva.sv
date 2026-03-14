module mux4to1_sva (
    input  logic CLK,
    input  logic RESETn,
    input  logic in0,
    input  logic in1,
    input  logic in2,
    input  logic in3,
    input  logic sel0,
    input  logic sel1,
    input  logic out
);
    // When sel=00, out must equal in0.
    check_sel00_path: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ({sel1, sel0} == 2'b00) |-> (out == in0)
    );

    // When sel=01, out must equal in1.
    check_sel01_path: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ({sel1, sel0} == 2'b01) |-> (out == in1)
    );

    // When sel=10, out must equal in2.
    check_sel10_path: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ({sel1, sel0} == 2'b10) |-> (out == in2)
    );

    // When sel=11, out must equal in3.
    check_sel11_path: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ({sel1, sel0} == 2'b11) |-> (out == in3)
    );

    // If all inputs and selects are stable, out must be stable.
    check_out_stable_when_all_stable: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ($stable(in0) && $stable(in1) && $stable(in2) && $stable(in3) && $stable(sel0) && $stable(sel1)) |-> $stable(out)
    );

    // If selects are stable and the selected input is stable, out must be stable.
    check_out_stable_when_sel_and_selected_input_stable: assert property (
        @(posedge CLK) disable iff (!RESETn)
        ($stable(sel0) && $stable(sel1) &&
         ((({sel1,sel0} == 2'b00) && $stable(in0)) ||
          (({sel1,sel0} == 2'b01) && $stable(in1)) ||
          (({sel1,sel0} == 2'b10) && $stable(in2)) ||
          (({sel1,sel0} == 2'b11) && $stable(in3)))) |-> $stable(out)
    );

    // Any output change must be caused by a select change or the selected input change.
    check_out_change_has_cause: assert property (
        @(posedge CLK) disable iff (!RESETn)
        $changed(out) |-> (
            $changed(sel0) || $changed(sel1) ||
            (({sel1,sel0} == 2'b00) && $changed(in0)) ||
            (({sel1,sel0} == 2'b01) && $changed(in1)) ||
            (({sel1,sel0} == 2'b10) && $changed(in2)) ||
            (({sel1,sel0} == 2'b11) && $changed(in3))
        )
    );
endmodule