module top_module_assertions (
    input logic clk,
    input logic [2:0] vec,
    input logic [2:0] outv,
    input logic o2,
    input logic o1,
    input logic o0
);

    // o0 is a direct copy of vec[0].
    check_o0_passthrough: assert property (
        @(posedge clk) o0 == vec[0]
    );

    // o1 is a direct copy of vec[1].
    check_o1_passthrough: assert property (
        @(posedge clk) o1 == vec[1]
    );

    // o2 is a direct copy of vec[2].
    check_o2_passthrough: assert property (
        @(posedge clk) o2 == vec[2]
    );

    // For vec=000, outv passes through unchanged.
    check_outv_when_vec_000: assert property (
        @(posedge clk) (vec == 3'b000) |-> (outv == vec)
    );

    // For vec=001, outv follows the specified permutation.
    check_outv_when_vec_001: assert property (
        @(posedge clk) (vec == 3'b001) |-> (outv == {vec[0], vec[2], vec[1]})
    );

    // For vec=010, outv follows the specified permutation.
    check_outv_when_vec_010: assert property (
        @(posedge clk) (vec == 3'b010) |-> (outv == {vec[1], vec[0], vec[2]})
    );

    // For vec=011, outv follows the specified permutation.
    check_outv_when_vec_011: assert property (
        @(posedge clk) (vec == 3'b011) |-> (outv == {vec[1], vec[2], vec[0]})
    );

    // For vec=100, outv follows the specified permutation.
    check_outv_when_vec_100: assert property (
        @(posedge clk) (vec == 3'b100) |-> (outv == {vec[2], vec[0], vec[1]})
    );

    // For vec=101, outv follows the specified permutation.
    check_outv_when_vec_101: assert property (
        @(posedge clk) (vec == 3'b101) |-> (outv == {vec[2], vec[1], vec[0]})
    );

    // For vec=110, the default case passes vec through unchanged.
    check_outv_when_vec_110: assert property (
        @(posedge clk) (vec == 3'b110) |-> (outv == vec)
    );

    // For vec=111, the default case passes vec through unchanged.
    check_outv_when_vec_111: assert property (
        @(posedge clk) (vec == 3'b111) |-> (outv == vec)
    );

endmodule