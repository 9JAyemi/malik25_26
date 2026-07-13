module math_ops_assertions (
    input logic       clk,
    input logic       reset,
    input logic [1:0] cos,
    input logic [1:0] one,
    input logic [1:0] s1,
    input logic [1:0] s2,
    input logic [1:0] s1_out,
    input logic [1:0] s2_out
);

    typedef logic [1:0] u2_t;

    logic [2:0] pipe_valid = 3'b000;

    always @(posedge clk) begin
        if (reset)
            pipe_valid <= 3'b000;
        else
            pipe_valid <= {pipe_valid[1:0], 1'b1};
    end

    function automatic u2_t add2(input u2_t a, input u2_t b);
        add2 = a + b;
    endfunction

    function automatic u2_t mul2(input u2_t a, input u2_t b);
        mul2 = a * b;
    endfunction

    // s1_out follows the registered add/multiply pipeline.
    check_s1_out_pipeline_function: assert property (
        @(posedge clk) disable iff (reset)
        pipe_valid[2] |-> s1_out == add2(
            mul2(add2($past(cos,3), $past(one,3)), $past(s2,2)),
            mul2($past(cos,2), $past(s1,2))
        )
    );

    // s2_out follows the registered add/multiply pipeline.
    check_s2_out_pipeline_function: assert property (
        @(posedge clk) disable iff (reset)
        pipe_valid[2] |-> s2_out == add2(
            mul2(add2($past(one,3), $past(cos,3)), $past(s1,2)),
            mul2($past(cos,2), $past(s2,2))
        )
    );

    // Matching delayed s1 and s2 produce matching outputs.
    check_equal_delayed_inputs_give_equal_outputs: assert property (
        @(posedge clk) disable iff (reset)
        pipe_valid[2] && ($past(s1,2) == $past(s2,2)) |-> (s1_out == s2_out)
    );

    // Zero delayed s1 and s2 force both outputs low.
    check_zero_delayed_inputs_force_zero_outputs: assert property (
        @(posedge clk) disable iff (reset)
        pipe_valid[2] && ($past(s1,2) == 2'b00) && ($past(s2,2) == 2'b00) |->
        (s1_out == 2'b00) && (s2_out == 2'b00)
    );

    // Zero delayed cos and one remove the x2/x6 paths.
    check_zero_old_add_stage_removes_cross_paths: assert property (
        @(posedge clk) disable iff (reset)
        pipe_valid[2] && ($past(cos,3) == 2'b00) && ($past(one,3) == 2'b00) |->
        (s1_out == mul2($past(cos,2), $past(s1,2))) &&
        (s2_out == mul2($past(cos,2), $past(s2,2)))
    );

    // Zero delayed cos removes the x3/x7 paths.
    check_zero_direct_cos_term_removes_direct_paths: assert property (
        @(posedge clk) disable iff (reset)
        pipe_valid[2] && ($past(cos,2) == 2'b00) |->
        (s1_out == mul2(add2($past(cos,3), $past(one,3)), $past(s2,2))) &&
        (s2_out == mul2(add2($past(cos,3), $past(one,3)), $past(s1,2)))
    );

endmodule