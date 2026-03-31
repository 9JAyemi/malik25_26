module bitwise_operators_sva #(
    parameter int n = 4
) (
    input logic clk,
    input logic [n-1:0] A,
    input logic [n-1:0] B,
    input logic [n-1:0] and_res,
    input logic [n-1:0] or_res,
    input logic [n-1:0] xor_res,
    input logic [n-1:0] not_res
);

    // and_res must equal the bitwise AND of A and B.
    check_and_result: assert property (
        @(posedge clk) and_res == (A & B)
    );

    // or_res must equal the bitwise OR of A and B.
    check_or_result: assert property (
        @(posedge clk) or_res == (A | B)
    );

    // xor_res must equal the bitwise XOR of A and B.
    check_xor_result: assert property (
        @(posedge clk) xor_res == (A ^ B)
    );

    // not_res must equal the bitwise NOT of A.
    check_not_result: assert property (
        @(posedge clk) not_res == (~A)
    );

    // The outputs must remain stable when A and B are stable.
    check_outputs_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B)) |-> $stable({and_res, or_res, xor_res, not_res})
    );

endmodule