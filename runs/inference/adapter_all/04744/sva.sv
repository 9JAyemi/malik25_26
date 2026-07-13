module mux_4to1_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] select,
    input logic [3:0] out
);
    // When select==00, out equals in0.
    check_sel00_routes_in0: assert property (
        @(posedge select[0] or negedge select[0] or posedge select[1] or negedge select[1])
        (select == 2'b00) |-> (out == in0)
    );

    // When select==01, out equals in1.
    check_sel01_routes_in1: assert property (
        @(posedge select[0] or negedge select[0] or posedge select[1] or negedge select[1])
        (select == 2'b01) |-> (out == in1)
    );

    // When select==10, out equals in2.
    check_sel10_routes_in2: assert property (
        @(posedge select[0] or negedge select[0] or posedge select[1] or negedge select[1])
        (select == 2'b10) |-> (out == in2)
    );

    // When select==11, out equals in3.
    check_sel11_routes_in3: assert property (
        @(posedge select[0] or negedge select[0] or posedge select[1] or negedge select[1])
        (select == 2'b11) |-> (out == in3)
    );

    // If select and all inputs are stable, out remains stable.
    check_stability_when_inputs_stable: assert property (
        @(posedge select[0] or negedge select[0] or posedge select[1] or negedge select[1])
        $stable(select) && $stable(in0) && $stable(in1) && $stable(in2) && $stable(in3) |-> $stable(out)
    );

    // If select==00 and only in0 changes, out changes to match.
    check_in0_change_propagates_when_sel00: assert property (
        @(posedge select[0] or negedge select[0] or posedge select[1] or negedge select[1])
        (select == 2'b00) && $stable(select) && $changed(in0) |-> $changed(out) && (out == in0)
    );

    // If select==01 and only in1 changes, out changes to match.
    check_in1_change_propagates_when_sel01: assert property (
        @(posedge select[0] or negedge select[0] or posedge select[1] or negedge select[1])
        (select == 2'b01) && $stable(select) && $changed(in1) |-> $changed(out) && (out == in1)
    );

    // If select==10 and only in2 changes, out changes to match.
    check_in2_change_propagates_when_sel10: assert property (
        @(posedge select[0] or negedge select[0] or posedge select[1] or negedge select[1])
        (select == 2'b10) && $stable(select) && $changed(in2) |-> $changed(out) && (out == in2)
    );

    // If select==11 and only in3 changes, out changes to match.
    check_in3_change_propagates_when_sel11: assert property (
        @(posedge select[0] or negedge select[0] or posedge select[1] or negedge select[1])
        (select == 2'b11) && $stable(select) && $changed(in3) |-> $changed(out) && (out == in3)
    );

    // If select==00 and in0 changes while select and in1/in2/in3 are stable, out holds.
    check_out_stable_when_sel00_and_in0_changes: assert property (
        @(posedge select[0] or negedge select[0] or posedge select[1] or negedge select[1])
        (select == 2'b00) && $stable(select) && $changed(in0) && $stable(in1) && $stable(in2) && $stable(in3) |-> $stable(out)
    );

    // If select==01 and in1 changes while select and in0/in2/in3 are stable, out holds.
    check_out_stable_when_sel01_and_in1_changes: assert property (
        @(posedge select[0] or negedge select[0] or posedge select[1] or negedge select[1])
        (select == 2'b01) && $stable(select) && $changed(in1) && $stable(in0) && $stable(in2) && $stable(in3) |-> $stable(out)
    );

    // If select==10 and in2 changes while select and in0/in1/in3 are stable, out holds.
    check_out_stable_when_sel10_and_in2_changes: assert property (
        @(posedge select[0] or negedge select[0] or posedge select[1] or negedge select[1])
        (select == 2'b10) && $stable(select) && $changed(in2) && $stable(in0) && $stable(in1) && $stable(in3) |-> $stable(out)
    );

    // If select==11 and in3 changes while select and in0/in1/in2 are stable, out holds.
    check_out_stable_when_sel11_and_in3_changes: assert property (
        @(posedge select[0] or negedge select[0] or posedge select[1] or negedge select[1])
        (select == 2'b11) && $stable(select) && $changed(in3) && $stable(in0) && $stable(in1) && $stable(in2) |-> $stable(out)
    );
endmodule