module mux4to1_sva (
    input logic clk,
    input logic out,
    input logic in0,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic [1:0] sel
);

    // When sel is 00, out must equal in0.
    check_sel_00_routes_in0: assert property (
        @(posedge clk) (sel === 2'b00) |-> (out === in0)
    );

    // When sel is 01, out must equal in1.
    check_sel_01_routes_in1: assert property (
        @(posedge clk) (sel === 2'b01) |-> (out === in1)
    );

    // When sel is 10, out must equal in2.
    check_sel_10_routes_in2: assert property (
        @(posedge clk) (sel === 2'b10) |-> (out === in2)
    );

    // When sel is 11, out must equal in3.
    check_sel_11_routes_in3: assert property (
        @(posedge clk) (sel === 2'b11) |-> (out === in3)
    );

    // For any non-binary sel value, the default case drives out low.
    check_default_drives_low: assert property (
        @(posedge clk)
        (!(sel === 2'b00) && !(sel === 2'b01) && !(sel === 2'b10) && !(sel === 2'b11))
        |-> (out === 1'b0)
    );

endmodule