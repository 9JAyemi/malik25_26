module mux4to1_sva (
    input logic       clk,
    input logic [3:0] in,
    input logic [1:0] sel,
    input logic       out
);

    // sel=00 routes in[0] to out.
    check_sel_00_routes_in0: assert property (
        @(posedge clk) (sel === 2'b00) |-> (out === in[0])
    );

    // sel=01 routes in[1] to out.
    check_sel_01_routes_in1: assert property (
        @(posedge clk) (sel === 2'b01) |-> (out === in[1])
    );

    // sel=10 routes in[2] to out.
    check_sel_10_routes_in2: assert property (
        @(posedge clk) (sel === 2'b10) |-> (out === in[2])
    );

    // sel=11 routes in[3] to out.
    check_sel_11_routes_in3: assert property (
        @(posedge clk) (sel === 2'b11) |-> (out === in[3])
    );

    // Any non-matching select value drives the default output of 0.
    check_default_out_zero: assert property (
        @(posedge clk)
        !((sel === 2'b00) || (sel === 2'b01) || (sel === 2'b10) || (sel === 2'b11))
        |-> (out === 1'b0)
    );

    // out always matches the mux case selection.
    check_full_mux_behavior: assert property (
        @(posedge clk)
        out === ((sel === 2'b00) ? in[0] :
                 (sel === 2'b01) ? in[1] :
                 (sel === 2'b10) ? in[2] :
                 (sel === 2'b11) ? in[3] :
                                   1'b0)
    );

endmodule