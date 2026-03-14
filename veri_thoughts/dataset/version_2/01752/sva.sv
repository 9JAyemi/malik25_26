module MUX4_1_sva (
    input logic CLK,
    input logic x0,
    input logic x1,
    input logic x2,
    input logic x3,
    input logic s0,
    input logic s1,
    input logic y
);
    // When s1s0==00, y equals x0.
    mux_sel_00: assert property (
        @(posedge CLK) (s1 == 1'b0 && s0 == 1'b0) |-> (y === x0)
    );

    // When s1s0==01, y equals x1.
    mux_sel_01: assert property (
        @(posedge CLK) (s1 == 1'b0 && s0 == 1'b1) |-> (y === x1)
    );

    // When s1s0==10, y equals x2.
    mux_sel_10: assert property (
        @(posedge CLK) (s1 == 1'b1 && s0 == 1'b0) |-> (y === x2)
    );

    // When s1s0==11, y equals x3.
    mux_sel_11: assert property (
        @(posedge CLK) (s1 == 1'b1 && s0 == 1'b1) |-> (y === x3)
    );
endmodule