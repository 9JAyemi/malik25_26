module mux4to1_sva (
    input  logic CLK,
    input  logic [7:0] in0,
    input  logic [7:0] in1,
    input  logic [7:0] in2,
    input  logic [7:0] in3,
    input  logic [1:0] sel,
    input  logic [7:0] out
);
    ///// Functional mapping /////
    // Out equals the ternary selection of inputs based on sel.
    check_mux_function: assert property (
        @(posedge CLK)
        out == ((sel == 2'b00) ? in0 :
                (sel == 2'b01) ? in1 :
                (sel == 2'b10) ? in2 : in3)
    );

    // When sel==00, out == in0.
    check_sel00_routes_in0: assert property (
        @(posedge CLK) (sel == 2'b00) |-> (out == in0)
    );

    // When sel==01, out == in1.
    check_sel01_routes_in1: assert property (
        @(posedge CLK) (sel == 2'b01) |-> (out == in1)
    );

    // When sel==10, out == in2.
    check_sel10_routes_in2: assert property (
        @(posedge CLK) (sel == 2'b10) |-> (out == in2)
    );

    // When sel==11, out == in3.
    check_sel11_routes_in3: assert property (
        @(posedge CLK) (sel == 2'b11) |-> (out == in3)
    );

    ///// Change propagation when selected /////
    // If in0 changes while selected, out matches in0.
    check_change_in0_updates_out_when_selected: assert property (
        @(posedge CLK) (sel == 2'b00 && $changed(in0)) |-> (out == in0)
    );

    // If in1 changes while selected, out matches in1.
    check_change_in1_updates_out_when_selected: assert property (
        @(posedge CLK) (sel == 2'b01 && $changed(in1)) |-> (out == in1)
    );

    // If in2 changes while selected, out matches in2.
    check_change_in2_updates_out_when_selected: assert property (
        @(posedge CLK) (sel == 2'b10 && $changed(in2)) |-> (out == in2)
    );

    // If in3 changes while selected, out matches in3.
    check_change_in3_updates_out_when_selected: assert property (
        @(posedge CLK) (sel == 2'b11 && $changed(in3)) |-> (out == in3)
    );
endmodule