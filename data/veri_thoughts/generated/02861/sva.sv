module mux4to1_sva (
    input logic CLK,
    input logic [3:0] data_in,
    input logic [1:0] sel,
    input logic out
);
    // Output equals the selected input bit for all sel values.
    check_mux_function: assert property (
        @(posedge CLK) out == ((sel == 2'b00) ? data_in[0] :
                               (sel == 2'b01) ? data_in[1] :
                               (sel == 2'b10) ? data_in[2] : data_in[3])
    );

    // When sel==2'b00, out equals data_in[0].
    check_sel_00: assert property (
        @(posedge CLK) (sel == 2'b00) |-> (out == data_in[0])
    );

    // When sel==2'b01, out equals data_in[1].
    check_sel_01: assert property (
        @(posedge CLK) (sel == 2'b01) |-> (out == data_in[1])
    );

    // When sel==2'b10, out equals data_in[2].
    check_sel_10: assert property (
        @(posedge CLK) (sel == 2'b10) |-> (out == data_in[2])
    );

    // When sel==2'b11, out equals data_in[3].
    check_sel_11: assert property (
        @(posedge CLK) (sel == 2'b11) |-> (out == data_in[3])
    );

    // If sel is stable and the selected input changes, out follows that new value.
    check_out_follows_selected_change: assert property (
        @(posedge CLK) $stable(sel) && (data_in[sel] != $past(data_in[sel])) |-> (out == data_in[sel])
    );

    // If sel is stable and out changes, the selected input must have changed.
    check_out_change_requires_selected_change: assert property (
        @(posedge CLK) $stable(sel) && (out != $past(out)) |-> (data_in[sel] != $past(data_in[sel]))
    );

    // If sel and the selected input are both stable, out remains stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge CLK) $stable(sel) && $stable(data_in[sel]) |-> $stable(out)
    );
endmodule