module mux3_sva (
    input logic clk,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic [1:0] sel,
    input logic clr,
    input logic set,
    input logic out
);

    // out matches the combinational priority mux function.
    check_mux_function: assert property (
        @(posedge clk)
        out == (set ? 1'b1 :
                (clr ? 1'b0 :
                 ((sel == 2'b00) ? in0 :
                  ((sel == 2'b01) ? in1 :
                   ((sel == 2'b10) ? in2 : 1'b0)))))
    );

    // set has highest priority and forces out high.
    check_set_priority: assert property (
        @(posedge clk)
        set |-> (out == 1'b1)
    );

    // clr forces out low when set is low.
    check_clr_priority: assert property (
        @(posedge clk)
        (!set && clr) |-> (out == 1'b0)
    );

    // sel 00 passes in0 when set and clr are low.
    check_sel_in0: assert property (
        @(posedge clk)
        (!set && !clr && (sel == 2'b00)) |-> (out == in0)
    );

    // sel 01 passes in1 when set and clr are low.
    check_sel_in1: assert property (
        @(posedge clk)
        (!set && !clr && (sel == 2'b01)) |-> (out == in1)
    );

    // sel 10 passes in2 when set and clr are low.
    check_sel_in2: assert property (
        @(posedge clk)
        (!set && !clr && (sel == 2'b10)) |-> (out == in2)
    );

    // sel 11 forces out low when set and clr are low.
    check_sel_11_zero: assert property (
        @(posedge clk)
        (!set && !clr && (sel == 2'b11)) |-> (out == 1'b0)
    );

endmodule