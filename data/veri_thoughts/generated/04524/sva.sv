module mux_4to1_if_else_sva (
    input logic clk,
    input logic [1:0] a,
    input logic [1:0] b,
    input logic [1:0] sel,
    input logic [1:0] out
);

    // No reset in the RTL; sample combinational behavior on clk.

    // When sel is 2'b00, out must equal a.
    check_select_a: assert property (
        @(posedge clk) (sel == 2'b00) |-> (out == a)
    );

    // When sel is 2'b01, out must equal b.
    check_select_b: assert property (
        @(posedge clk) (sel == 2'b01) |-> (out == b)
    );

    // When sel is 2'b10, out must equal a & b.
    check_select_and: assert property (
        @(posedge clk) (sel == 2'b10) |-> (out == (a & b))
    );

    // When sel is 2'b11, out must equal a | b.
    check_select_or: assert property (
        @(posedge clk) (sel == 2'b11) |-> (out == (a | b))
    );

    // Out must always match the full mux function.
    check_mux_function: assert property (
        @(posedge clk) out == ((sel == 2'b00) ? a :
                               (sel == 2'b01) ? b :
                               (sel == 2'b10) ? (a & b) :
                                                (a | b))
    );

endmodule