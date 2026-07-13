module pipelined_module_sva (
    input logic [2:0] in_vec,
    input logic [2:0] out_vec,
    input logic o2,
    input logic o1,
    input logic o0,
    input logic clk,
    input logic [2:0] reg1_out,
    input logic [2:0] reg2_out,
    input logic [2:0] in_reg,
    input logic [2:0] reg1_reg,
    input logic [2:0] reg2_reg
);

    // out_vec is directly driven by reg2_out.
    check_out_vec_matches_reg2_out: assert property (
        @(posedge clk) (out_vec == reg2_out)
    );

    // The scalar outputs are the bits of reg2_out.
    check_scalar_outputs_match_reg2_out: assert property (
        @(posedge clk) ({o2, o1, o0} == reg2_out)
    );

    // in_reg captures in_vec on the previous clock.
    check_in_reg_captures_input: assert property (
        @(posedge clk) (!$initstate) |-> (in_reg == $past(in_vec))
    );

    // reg1_reg captures in_reg on the previous clock.
    check_reg1_reg_captures_in_reg: assert property (
        @(posedge clk) (!$initstate) |-> (reg1_reg == $past(in_reg))
    );

    // reg1_out is the registered output of stage1 from in_reg.
    check_reg1_out_captures_in_reg: assert property (
        @(posedge clk) (!$initstate) |-> (reg1_out == $past(in_reg))
    );

    // reg2_out is the registered output of stage2 from reg1_reg.
    check_reg2_out_captures_reg1_reg: assert property (
        @(posedge clk) (!$initstate) |-> (reg2_out == $past(reg1_reg))
    );

    // reg2_reg captures reg1_out on the previous clock.
    check_reg2_reg_captures_reg1_out: assert property (
        @(posedge clk) (!$initstate) |-> (reg2_reg == $past(reg1_out))
    );

    // reg1_reg and reg1_out carry the same delayed value after the first clock.
    check_reg1_reg_matches_reg1_out: assert property (
        @(posedge clk) (!$initstate) |-> (reg1_reg == reg1_out)
    );

    // reg2_reg and reg2_out align once the previous stage has settled.
    check_reg2_reg_matches_reg2_out: assert property (
        @(posedge clk) (!$initstate && !$past($initstate)) |-> (reg2_reg == reg2_out)
    );

    // out_vec reflects in_vec after three sampled clock edges.
    check_output_three_cycle_latency: assert property (
        @(posedge clk) (!$initstate && !$past($initstate) && !$past($initstate,2))
        |-> (out_vec == $past(in_vec, 3))
    );

endmodule

bind pipelined_module pipelined_module_sva pipelined_module_sva_inst (
    .in_vec(in_vec),
    .out_vec(out_vec),
    .o2(o2),
    .o1(o1),
    .o0(o0),
    .clk(clk),
    .reg1_out(reg1_out),
    .reg2_out(reg2_out),
    .in_reg(in_reg),
    .reg1_reg(reg1_reg),
    .reg2_reg(reg2_reg)
);