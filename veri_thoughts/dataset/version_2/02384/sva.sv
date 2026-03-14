module mux_2_1_sva (
    input logic [1:0] in,
    input logic sel,
    input logic out
);
    // out equals selected input (2:1 mux function) on any input or select edge.
    check_mux_function: assert property (
        @(posedge sel or negedge sel or posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
            out == ((sel == 1'b0) ? in[0] : in[1])
    );

    // On rising sel, out reflects in[1].
    check_out_on_sel_rise: assert property (
        @(posedge sel) out == in[1]
    );

    // On falling sel, out reflects in[0].
    check_out_on_sel_fall: assert property (
        @(negedge sel) out == in[0]
    );

    // If sel is 0 and in[0] toggles, out follows in[0].
    check_out_follows_in0_when_sel0: assert property (
        @(posedge in[0] or negedge in[0]) (sel == 1'b0) |-> (out == in[0])
    );

    // If sel is 1 and in[1] toggles, out follows in[1].
    check_out_follows_in1_when_sel1: assert property (
        @(posedge in[1] or negedge in[1]) (sel == 1'b1) |-> (out == in[1])
    );

    // When both inputs are equal, out equals that common value.
    check_out_when_inputs_equal: assert property (
        @(posedge sel or negedge sel or posedge in[0] or negedge in[0] or posedge in[1] or negedge in[1])
            (in[0] == in[1]) |-> (out == in[0])
    );
endmodule