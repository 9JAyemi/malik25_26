module top_module_assertions (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic C,
    input logic select,
    input logic [3:0] out
);

    // Check the direct add path when select is low.
    check_direct_add_path: assert property (
        @(posedge clk) (!select && C) |-> (out == (A + B))
    );

    // Check the direct subtract path when select is low.
    check_direct_sub_path: assert property (
        @(posedge clk) (!select && !C) |-> (out == (A - B))
    );

    // Check the two's complement of the add result when select is high.
    check_twos_comp_add_path: assert property (
        @(posedge clk) (select && C) |-> (out == ((~(A + B)) + 4'b0001))
    );

    // Check the two's complement of the subtract result when select is high.
    check_twos_comp_sub_path: assert property (
        @(posedge clk) (select && !C) |-> (out == ((~(A - B)) + 4'b0001))
    );

    // Check the full output function for all input combinations.
    check_full_output_function: assert property (
        @(posedge clk)
        out == (select ? ((~(C ? (A + B) : (A - B))) + 4'b0001)
                       :  (C ? (A + B) : (A - B)))
    );

endmodule