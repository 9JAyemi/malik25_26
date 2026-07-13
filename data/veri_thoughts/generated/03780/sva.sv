module top_module_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic A,
    input logic B,
    input logic out
);

    // When select is 00, out is the inverse of a[0] & b[0].
    check_select_00_routes_bit0: assert property (
        @(posedge clk)
        ((A == 1'b0) && (B == 1'b0)) |-> (out === ~(a[0] & b[0]))
    );

    // When select is 01, out is the inverse of a[1] & b[1].
    check_select_01_routes_bit1: assert property (
        @(posedge clk)
        ((A == 1'b0) && (B == 1'b1)) |-> (out === ~(a[1] & b[1]))
    );

    // When select is 10, out is the inverse of a[2] & b[2].
    check_select_10_routes_bit2: assert property (
        @(posedge clk)
        ((A == 1'b1) && (B == 1'b0)) |-> (out === ~(a[2] & b[2]))
    );

    // When select is 11, out is the inverse of a[3] & b[3].
    check_select_11_routes_bit3: assert property (
        @(posedge clk)
        ((A == 1'b1) && (B == 1'b1)) |-> (out === ~(a[3] & b[3]))
    );

    // With select 00 and selected inputs stable, out stays stable.
    check_select_00_stability: assert property (
        @(posedge clk)
        ($stable(A) && $stable(B) && (A == 1'b0) && (B == 1'b0) &&
         $stable(a[0]) && $stable(b[0])) |-> $stable(out)
    );

    // With select 01 and selected inputs stable, out stays stable.
    check_select_01_stability: assert property (
        @(posedge clk)
        ($stable(A) && $stable(B) && (A == 1'b0) && (B == 1'b1) &&
         $stable(a[1]) && $stable(b[1])) |-> $stable(out)
    );

    // With select 10 and selected inputs stable, out stays stable.
    check_select_10_stability: assert property (
        @(posedge clk)
        ($stable(A) && $stable(B) && (A == 1'b1) && (B == 1'b0) &&
         $stable(a[2]) && $stable(b[2])) |-> $stable(out)
    );

    // With select 11 and selected inputs stable, out stays stable.
    check_select_11_stability: assert property (
        @(posedge clk)
        ($stable(A) && $stable(B) && (A == 1'b1) && (B == 1'b1) &&
         $stable(a[3]) && $stable(b[3])) |-> $stable(out)
    );

endmodule