module add_sub_8bit_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic sub,
    input logic [7:0] out
);
    // DUT has no clock/reset; pure combinational datapath. Sample properties on external clk.
    // Function: out = (sub ? A - B : A + B).

    // Out matches selected operation for all input combinations.
    check_out_matches_operation: assert property (
        @(posedge clk) out == (sub ? (A - B) : (A + B))
    );

    // With stable inputs, output remains stable (pure combinational function).
    check_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $stable(sub)) |-> $stable(out)
    );

    // In add mode, adding zero passes through A.
    check_add_zero_B: assert property (
        @(posedge clk) (sub == 1'b0 && B == 8'h00) |-> (out == A)
    );

    // In add mode, adding zero-A passes through B.
    check_add_zero_A: assert property (
        @(posedge clk) (sub == 1'b0 && A == 8'h00) |-> (out == B)
    );

    // In sub mode, subtracting zero passes through A.
    check_sub_zero_B: assert property (
        @(posedge clk) (sub == 1'b1 && B == 8'h00) |-> (out == A)
    );

    // In sub mode, subtracting equal operands yields zero.
    check_sub_equal_operands_zero: assert property (
        @(posedge clk) (sub == 1'b1 && (A == B)) |-> (out == 8'h00)
    );

    // On sub rising edge with A,B stable, output equals A - B.
    check_out_on_sub_rise: assert property (
        @(posedge clk) ($rose(sub) && $stable(A) && $stable(B)) |-> (out == (A - B))
    );

    // On sub falling edge with A,B stable, output equals A + B.
    check_out_on_sub_fall: assert property (
        @(posedge clk) ($fell(sub) && $stable(A) && $stable(B)) |-> (out == (A + B))
    );

    // In add mode, addition is commutative with respect to A and B.
    check_add_commutative: assert property (
        @(posedge clk) (sub == 1'b0) |-> (out == (B + A))
    );
endmodule