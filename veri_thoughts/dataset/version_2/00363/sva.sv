module mux_4to1_enable_assertions (
    input logic clk,
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic [3:0] in2,
    input logic [3:0] in3,
    input logic [1:0] sel,
    input logic en,
    input logic [3:0] out
);

    // External sampling clock for this combinational DUT.

    // When disabled, the output is forced to zero.
    check_disabled_forces_zero: assert property (
        @(posedge clk) (en === 1'b0) |-> (out === 4'b0000)
    );

    // With sel=00 and enable high, out follows in0.
    check_sel_00_routes_in0: assert property (
        @(posedge clk) ((sel === 2'b00) && (en === 1'b1)) |-> (out === in0)
    );

    // With sel=01 and enable high, out follows in1.
    check_sel_01_routes_in1: assert property (
        @(posedge clk) ((sel === 2'b01) && (en === 1'b1)) |-> (out === in1)
    );

    // With sel=10 and enable high, out follows in2.
    check_sel_10_routes_in2: assert property (
        @(posedge clk) ((sel === 2'b10) && (en === 1'b1)) |-> (out === in2)
    );

    // With sel=11 and enable high, out follows in3.
    check_sel_11_routes_in3: assert property (
        @(posedge clk) ((sel === 2'b11) && (en === 1'b1)) |-> (out === in3)
    );

    // Any non-matching select value drives the default zero output.
    check_invalid_sel_defaults_zero: assert property (
        @(posedge clk)
        !((sel === 2'b00) || (sel === 2'b01) || (sel === 2'b10) || (sel === 2'b11))
        |-> (out === 4'b0000)
    );

endmodule