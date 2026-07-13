module top_module_sva (
    input  logic CLK,
    input  logic RESETn,
    input  logic [3:0] a1,
    input  logic [3:0] a2,
    input  logic [3:0] b1,
    input  logic [3:0] b2,
    input  logic sel1,
    input  logic sel2,
    input  logic select,
    input  logic [3:0] out
);
    // Local replicas of combinational selections
    logic [3:0] sel1_mux;
    logic [3:0] sel2_mux;
    assign sel1_mux = (sel1 == 1'b0) ? a1 : b1;
    assign sel2_mux = (sel2 == 1'b0) ? a2 : b2;

    // When select is 1, output is forced to zero.
    check_select_one_forces_zero: assert property (
        @(posedge CLK) disable iff (!RESETn) (select == 1'b1) |-> (out == 4'b0)
    );

    // When select is 0, output equals selected difference.
    check_select_zero_general_diff: assert property (
        @(posedge CLK) disable iff (!RESETn) (select == 1'b0) |-> (out == (sel1_mux - sel2_mux))
    );

    // Case: select=0, sel1=0, sel2=0 -> out = a1 - a2.
    check_case_sel00: assert property (
        @(posedge CLK) disable iff (!RESETn) (select==1'b0 && sel1==1'b0 && sel2==1'b0) |-> (out == (a1 - a2))
    );

    // Case: select=0, sel1=1, sel2=0 -> out = b1 - a2.
    check_case_sel10: assert property (
        @(posedge CLK) disable iff (!RESETn) (select==1'b0 && sel1==1'b1 && sel2==1'b0) |-> (out == (b1 - a2))
    );

    // Case: select=0, sel1=0, sel2=1 -> out = a1 - b2.
    check_case_sel01: assert property (
        @(posedge CLK) disable iff (!RESETn) (select==1'b0 && sel1==1'b0 && sel2==1'b1) |-> (out == (a1 - b2))
    );

    // Case: select=0, sel1=1, sel2=1 -> out = b1 - b2.
    check_case_sel11: assert property (
        @(posedge CLK) disable iff (!RESETn) (select==1'b0 && sel1==1'b1 && sel2==1'b1) |-> (out == (b1 - b2))
    );

    // On rising edge of select, output must be zero (enable deasserted).
    check_out_zero_on_rose_select: assert property (
        @(posedge CLK) disable iff (!RESETn) $rose(select) |-> (out == 4'b0)
    );

    // On falling edge of select, output equals selected difference.
    check_out_diff_on_fell_select: assert property (
        @(posedge CLK) disable iff (!RESETn) $fell(select) |-> (out == (sel1_mux - sel2_mux))
    );

    // If a1==b1 and select==0, output uses a1 regardless of sel1.
    check_independence_sel1_when_a1_eq_b1: assert property (
        @(posedge CLK) disable iff (!RESETn) (select==1'b0 && (a1==b1)) |-> (out == (a1 - sel2_mux))
    );

    // If a2==b2 and select==0, output uses a2 regardless of sel2.
    check_independence_sel2_when_a2_eq_b2: assert property (
        @(posedge CLK) disable iff (!RESETn) (select==1'b0 && (a2==b2)) |-> (out == (sel1_mux - a2))
    );
endmodule