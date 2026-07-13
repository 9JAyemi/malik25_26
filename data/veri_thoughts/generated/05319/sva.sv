module mux_4to1_sva (
    input logic       clk,
    input logic [1:0] sel,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [3:0] c,
    input logic [3:0] d,
    input logic [1:0] out
);

    // The mux output must match the currently selected input slice.
    check_mux_mapping: assert property (
        @(posedge clk)
        ((sel === 2'b00) ? (out === a[1:0]) :
         (sel === 2'b01) ? (out === b[1:0]) :
         (sel === 2'b10) ? (out === c[1:0]) :
         (sel === 2'b11) ? (out === d[1:0]) :
         1'b1)
    );

    // sel=00 selects a[1:0].
    check_select_a: assert property (
        @(posedge clk) (sel === 2'b00) |-> (out === a[1:0])
    );

    // sel=01 selects b[1:0].
    check_select_b: assert property (
        @(posedge clk) (sel === 2'b01) |-> (out === b[1:0])
    );

    // sel=10 selects c[1:0].
    check_select_c: assert property (
        @(posedge clk) (sel === 2'b10) |-> (out === c[1:0])
    );

    // sel=11 selects d[1:0].
    check_select_d: assert property (
        @(posedge clk) (sel === 2'b11) |-> (out === d[1:0])
    );

endmodule