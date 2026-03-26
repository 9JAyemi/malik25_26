module mux4to1_sva (
    input logic clk,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic [1:0] sel,
    input logic out
);

    // out follows in0 when sel selects input 0.
    check_sel_00_routes_in0: assert property (
        @(posedge clk) (sel === 2'b00) |-> (out === in0)
    );

    // out follows in1 when sel selects input 1.
    check_sel_01_routes_in1: assert property (
        @(posedge clk) (sel === 2'b01) |-> (out === in1)
    );

    // out follows in2 when sel selects input 2.
    check_sel_10_routes_in2: assert property (
        @(posedge clk) (sel === 2'b10) |-> (out === in2)
    );

    // out follows in3 when sel selects input 3.
    check_sel_11_routes_in3: assert property (
        @(posedge clk) (sel === 2'b11) |-> (out === in3)
    );

    // out stays stable when sel remains on input 0 and in0 is stable.
    check_sel_00_out_stable_with_stable_in0: assert property (
        @(posedge clk)
        (!$initstate && ($past(sel) === 2'b00) && (sel === 2'b00) && ($past(in0) === in0))
        |-> ($past(out) === out)
    );

    // out stays stable when sel remains on input 1 and in1 is stable.
    check_sel_01_out_stable_with_stable_in1: assert property (
        @(posedge clk)
        (!$initstate && ($past(sel) === 2'b01) && (sel === 2'b01) && ($past(in1) === in1))
        |-> ($past(out) === out)
    );

    // out stays stable when sel remains on input 2 and in2 is stable.
    check_sel_10_out_stable_with_stable_in2: assert property (
        @(posedge clk)
        (!$initstate && ($past(sel) === 2'b10) && (sel === 2'b10) && ($past(in2) === in2))
        |-> ($past(out) === out)
    );

    // out stays stable when sel remains on input 3 and in3 is stable.
    check_sel_11_out_stable_with_stable_in3: assert property (
        @(posedge clk)
        (!$initstate && ($past(sel) === 2'b11) && (sel === 2'b11) && ($past(in3) === in3))
        |-> ($past(out) === out)
    );

endmodule