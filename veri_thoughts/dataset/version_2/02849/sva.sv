module top_module_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic xor_out,
    input logic cout,
    input logic sum
);
    // xor_out must equal a ^ b.
    check_xor_out_function: assert property (
        @(posedge clk) xor_out === (a ^ b)
    );

    // sum must equal a ^ b.
    check_sum_function: assert property (
        @(posedge clk) sum === (a ^ b)
    );

    // cout must equal a & b.
    check_cout_function: assert property (
        @(posedge clk) cout === (a & b)
    );

    // sum must mirror xor_out.
    check_sum_equals_xor_out: assert property (
        @(posedge clk) sum === xor_out
    );

    // Truth table: a=0,b=0 -> xor_out=0,sum=0,cout=0.
    check_tt_00: assert property (
        @(posedge clk) (a === 1'b0 && b === 1'b0) |-> (xor_out === 1'b0 && sum === 1'b0 && cout === 1'b0)
    );

    // Truth table: a=1,b=1 -> xor_out=0,sum=0,cout=1.
    check_tt_11: assert property (
        @(posedge clk) (a === 1'b1 && b === 1'b1) |-> (xor_out === 1'b0 && sum === 1'b0 && cout === 1'b1)
    );

    // Truth table: a=1,b=0 -> xor_out=1,sum=1,cout=0.
    check_tt_10: assert property (
        @(posedge clk) (a === 1'b1 && b === 1'b0) |-> (xor_out === 1'b1 && sum === 1'b1 && cout === 1'b0)
    );

    // Truth table: a=0,b=1 -> xor_out=1,sum=1,cout=0.
    check_tt_01: assert property (
        @(posedge clk) (a === 1'b0 && b === 1'b1) |-> (xor_out === 1'b1 && sum === 1'b1 && cout === 1'b0)
    );

    // When cout is 1, sum must be 0.
    check_cout1_implies_sum0: assert property (
        @(posedge clk) (cout === 1'b1) |-> (sum === 1'b0)
    );

    // When sum is 1, cout must be 0.
    check_sum1_implies_cout0: assert property (
        @(posedge clk) (sum === 1'b1) |-> (cout === 1'b0)
    );
endmodule