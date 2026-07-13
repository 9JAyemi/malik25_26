module comparator_4bit_sva (
    input logic [3:0] in0,
    input logic [3:0] in1,
    input logic       clk,
    input logic [1:0] out,
    input logic [3:0] reg_in0,
    input logic [3:0] reg_in1,
    input logic [1:0] reg_out
);

    // reg_in0 captures in0 on the prior clock.
    check_reg_in0_samples_in0: assert property (
        @(posedge clk) 1'b1 |=> (reg_in0 === $past(in0))
    );

    // reg_in1 captures in1 on the prior clock.
    check_reg_in1_samples_in1: assert property (
        @(posedge clk) 1'b1 |=> (reg_in1 === $past(in1))
    );

    // reg_out encodes less-than for the prior registered inputs.
    check_reg_out_less_than: assert property (
        @(posedge clk) (reg_in0 < reg_in1) |=> (reg_out === 2'b00)
    );

    // reg_out encodes equality for the prior registered inputs.
    check_reg_out_equal: assert property (
        @(posedge clk) (reg_in0 == reg_in1) |=> (reg_out === 2'b01)
    );

    // reg_out encodes greater-than for the prior registered inputs.
    check_reg_out_greater_than: assert property (
        @(posedge clk) (reg_in0 > reg_in1) |=> (reg_out === 2'b10)
    );

    // reg_out always uses one of the implemented encodings after the first update.
    check_reg_out_valid_encoding: assert property (
        @(posedge clk) 1'b1 |=> ((reg_out === 2'b00) || (reg_out === 2'b01) || (reg_out === 2'b10))
    );

    // out always mirrors reg_out.
    check_out_mirrors_reg_out: assert property (
        @(posedge clk) (out === reg_out)
    );

    // out reports less-than two clocks after the input comparison.
    check_out_less_than_latency: assert property (
        @(posedge clk) (in0 < in1) |-> ##2 (out === 2'b00)
    );

    // out reports equality two clocks after the input comparison.
    check_out_equal_latency: assert property (
        @(posedge clk) (in0 == in1) |-> ##2 (out === 2'b01)
    );

    // out reports greater-than two clocks after the input comparison.
    check_out_greater_than_latency: assert property (
        @(posedge clk) (in0 > in1) |-> ##2 (out === 2'b10)
    );

endmodule

bind comparator_4bit comparator_4bit_sva comparator_4bit_sva_inst (
    .in0(in0),
    .in1(in1),
    .clk(clk),
    .out(out),
    .reg_in0(reg_in0),
    .reg_in1(reg_in1),
    .reg_out(reg_out)
);