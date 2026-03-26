module mux_8bit_4to1_sva (
    input logic       clk,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    input logic [7:0] d,
    input logic [1:0] sel,
    input logic [7:0] out
);

    // RTL is combinational with no reset; clk is a sampling clock for these checks.

    // When sel selects a, out must equal a.
    check_select_a: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out == a)
    );

    // When sel selects b, out must equal b.
    check_select_b: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out == b)
    );

    // When sel selects c, out must equal c.
    check_select_c: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out == c)
    );

    // When sel selects d, out must equal d.
    check_select_d: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out == d)
    );

endmodule