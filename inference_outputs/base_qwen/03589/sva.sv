```systemverilog
module addsub_sva (
    input logic [3:0] A,
    input logic [3:0] B,
    input logic SUB,
    output logic [3:0] OUT,
    output logic COUT
);
    // No clock or reset signals present in the RTL

    // Combinational logic, so use @(posedge clk) for assertions

    // Check that COUT is set based on the sign bit of the result
    check_cout: assert property (
        @(posedge clk) $stable(A) && $stable(B) && $stable(SUB) |-> (COUT == ADD[3])
    ) else $error("COUT is not set based on the sign bit of the result");

    // Check that OUT is set correctly for addition
    check_addition: assert property (
        @(posedge clk) $stable(A) && $stable(B) && $stable(SUB) |-> (OUT == (SUB ? B_INV + 1 : ADD))
    ) else $error("OUT is not set correctly for addition");

    // Check that OUT is set correctly for subtraction
    check_subtraction: assert property (
        @(posedge clk) $stable(A) && $stable(B) && $stable(SUB) |-> (OUT == (SUB ? B_INV + 1 : ADD))
    ) else $error("OUT is not set correctly for subtraction");

    // Check that B_INV is the inverse of B
    check_b_inv: assert property (
        @(posedge clk) $stable(B) |-> (B_INV == ~B)
    ) else $error("B_INV is not the inverse of B");

    // Check that ADD is correctly calculated for addition
    check_add: assert property (
        @(posedge clk) $stable(A) && $stable(B) && $stable(SUB) |-> (ADD == (SUB ? A + B_INV : A + B))
    ) else $error("ADD is not correctly calculated for addition");

    // Check that ADD is correctly calculated for subtraction
    check_sub: assert property (
        @(posedge clk) $stable(A) && $stable(B) && $stable(SUB) |-> (ADD == (SUB ? A + B_INV : A + B))
    ) else $error("ADD is not correctly calculated for subtraction");

    // Check that SUB_NEG is the sign bit of ADD
    check_sub_neg: assert property (
        @(posedge clk) $stable(ADD) |-> (SUB_NEG == ADD[3])
    ) else $error("SUB_NEG is not the sign bit of ADD");

endmodule
```