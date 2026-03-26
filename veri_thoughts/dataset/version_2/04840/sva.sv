module binary_adder_sva(
    input logic [3:0] A,
    input logic [3:0] B,
    input logic control,
    input logic [3:0] C,
    input logic clk
);

    // In add mode, C equals the 4-bit sum of A and B.
    check_add_mode_result: assert property (
        @(posedge clk) (control == 1'b0) |-> (C == (A + B))
    );

    // In subtract mode, C equals the 4-bit difference of A and B.
    check_sub_mode_result: assert property (
        @(posedge clk) (control == 1'b1) |-> (C == (A - B))
    );

    // With unchanged inputs, the combinational output remains unchanged.
    check_output_stable_when_inputs_stable: assert property (
        @(posedge clk) ($stable(A) && $stable(B) && $stable(control)) |-> $stable(C)
    );

endmodule