module ternary_add_sva (
    input logic clk,
    input logic [WIDTH-1:0] a,
    input logic [WIDTH-1:0] b,
    input logic [WIDTH-1:0] c,
    input logic SIGN_EXT,
    output logic [WIDTH+1:0] o
);
    parameter WIDTH = 8;

    ///// Combinational logic /////
    // The output o is calculated based on the inputs a, b, c, and SIGN_EXT.
    // When SIGN_EXT is 0, o = a + b + c.
    // When SIGN_EXT is 1, o = {a[WIDTH-1],a[WIDTH-1],a} + {b[WIDTH-1],b[WIDTH-1],b} + {c[WIDTH-1],c[WIDTH-1],c}.
    comb_logic: assert property (
        @(posedge clk) disable iff (!SIGN_EXT) (o == a + b + c)
    ) else $error("Combinational logic error when SIGN_EXT is 0");

    sign_ext_logic: assert property (
        @(posedge clk) disable iff (SIGN_EXT) (o == {a[WIDTH-1],a[WIDTH-1],a} + {b[WIDTH-1],b[WIDTH-1],b} + {c[WIDTH-1],c[WIDTH-1],c})
    ) else $error("Combinational logic error when SIGN_EXT is 1");
endmodule