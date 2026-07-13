module mux4_sva (
    input logic clk,          // sampling clock for SVA
    input logic [3:0] in,
    input logic [1:0] sel,
    input logic out
);
    ///// Mux functional correctness /////
    // Out equals the selected input bit.
    check_mux_function: assert property (
        @(posedge clk) out == in[sel]
    );

    // When sel==00, out equals in[0].
    check_sel00_routes_in0: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out == in[0])
    );

    // When sel==01, out equals in[1].
    check_sel01_routes_in1: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out == in[1])
    );

    // When sel==10, out equals in[2].
    check_sel10_routes_in2: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out == in[2])
    );

    // When sel==11, out equals in[3].
    check_sel11_routes_in3: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out == in[3])
    );

    ///// Stability and independence /////
    // If sel and the selected input are stable, out must be stable.
    check_out_stable_when_sel_and_selected_stable: assert property (
        @(posedge clk) $stable(sel) && $stable(in[sel]) |-> $stable(out)
    );

    // If sel is stable and the selected input changes, out updates to the new selected input.
    check_out_follows_selected_input: assert property (
        @(posedge clk) $stable(sel) && (in[sel] != $past(in[sel])) |-> (out == in[sel])
    );

    // Changes on unselected inputs do not affect out when sel and selected input are stable.
    check_unselected_inputs_do_not_affect_out: assert property (
        @(posedge clk)
            $stable(sel) && $stable(in[sel]) &&
            (((in ^ $past(in)) & ~(4'b0001 << sel)) != 4'b0000)
            |-> $stable(out)
    );
endmodule