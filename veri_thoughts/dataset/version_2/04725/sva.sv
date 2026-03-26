module concat_AB_sva (
    input logic [3:0] A,
    input logic [1:0] B,
    input logic [2:0] Z
);

    // No clock or reset in RTL; sample combinational behavior on the formal global clock.

    // When A is greater than 7, Z must be forced to 3'b111.
    check_a_gt_7_forces_ones: assert property (
        @($global_clock) (A > 4'd7) |-> (Z == 3'b111)
    );

    // When A is 7 or less, Z must match the truncated concatenation result.
    check_a_le_7_truncated_concat: assert property (
        @($global_clock) !(A > 4'd7) |-> (Z == {B[0], A[1:0]})
    );

    // Z must always match the implemented combinational function.
    check_full_function: assert property (
        @($global_clock) Z == ((A > 4'd7) ? 3'b111 : {B[0], A[1:0]})
    );

endmodule