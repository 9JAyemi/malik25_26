module barrel_shifter_sva (
    input logic       clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] Q
);

    function automatic [3:0] expected_q;
        input [3:0] a;
        input [3:0] b;
        reg [3:0] s1;
        reg [3:0] s2;
        begin
            s1 = b[3] ? {a[2:0], 1'b0} : {1'b0, a[3:1]};
            s2 = b[2] ? {s1[1:0], 2'b00} : {2'b00, s1[3:2]};
            expected_q = b[1] ? {s2[0], s2[3:1]} : {s2[2:0], s2[3]};
        end
    endfunction

    // Q matches the full combinational transform.
    check_full_mapping: assert property (
        @(posedge clk) (Q == expected_q(A, B))
    );

    // B[0] is unused in the output computation.
    check_b0_unused: assert property (
        @(posedge clk)
        (Q == expected_q(A, {B[3:1], 1'b0})) &&
        (Q == expected_q(A, {B[3:1], 1'b1}))
    );

    // B[3:1]=000 selects right shift, right shift, then left rotate.
    check_ctrl_000_output: assert property (
        @(posedge clk) (B[3:1] == 3'b000) |-> (Q == {2'b00, A[3], 1'b0})
    );

    // B[3:1]=001 selects right shift, right shift, then right rotate.
    check_ctrl_001_output: assert property (
        @(posedge clk) (B[3:1] == 3'b001) |-> (Q == {A[3], 3'b000})
    );

    // B[3:1]=010 selects right shift, left shift, then left rotate.
    check_ctrl_010_output: assert property (
        @(posedge clk) (B[3:1] == 3'b010) |-> (Q == {A[1], 2'b00, A[2]})
    );

    // B[3:1]=011 selects right shift, left shift, then right rotate.
    check_ctrl_011_output: assert property (
        @(posedge clk) (B[3:1] == 3'b011) |-> (Q == {1'b0, A[2:1], 1'b0})
    );

    // B[3:1]=100 selects left shift, right shift, then left rotate.
    check_ctrl_100_output: assert property (
        @(posedge clk) (B[3:1] == 3'b100) |-> (Q == {1'b0, A[2:1], 1'b0})
    );

    // B[3:1]=101 selects left shift, right shift, then right rotate.
    check_ctrl_101_output: assert property (
        @(posedge clk) (B[3:1] == 3'b101) |-> (Q == {A[1], 2'b00, A[2]})
    );

    // B[3:1]=110 selects left shift, left shift, then left rotate.
    check_ctrl_110_output: assert property (
        @(posedge clk) (B[3:1] == 3'b110) |-> (Q == {3'b000, A[0]})
    );

    // B[3:1]=111 selects left shift, left shift, then right rotate.
    check_ctrl_111_output: assert property (
        @(posedge clk) (B[3:1] == 3'b111) |-> (Q == {1'b0, A[0], 2'b00})
    );

endmodule